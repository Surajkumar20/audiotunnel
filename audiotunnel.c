/*
 * audiotunnel.c -- route one app's audio (+ optionally your real mic) into a
 *                  virtual microphone on Windows.
 *
 *   [ chosen window's process tree ] --process loopback--\
 *                                                         >-- mix --> [ CABLE Input ]
 *   [ your real microphone ] ---------WASAPI capture-----/                  |
 *                                                                           v
 *                                                 WhatsApp mic = "CABLE Output"
 *
 * Windows cannot create a capture endpoint from user mode (that needs a signed
 * kernel driver), so the mixed signal is *rendered* into a virtual audio cable
 * (VB-CABLE / VoiceMeeter / any loopback driver). The cable's capture side then
 * shows up as a normal microphone in every app.
 *
 * Requires Windows 10 build 20348+ (per-process loopback API).
 *
 * Build:  gcc -O2 -o audiotunnel.exe audiotunnel.c -lole32 -loleaut32 -luser32 -lavrt
 */

#define WIN32_LEAN_AND_MEAN
#define COBJMACROS
#define CINTERFACE
#define _WIN32_WINNT 0x0A00

#include <windows.h>
#include <mmdeviceapi.h>
#include <audioclient.h>
#include <mmreg.h>
#include <objbase.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <conio.h>

/* ------------------------------------------------------------------ */
/* Bits the MinGW headers are missing (they live in the newest Win SDK) */
/* ------------------------------------------------------------------ */

#ifndef AUDCLNT_STREAMFLAGS_AUTOCONVERTPCM
#define AUDCLNT_STREAMFLAGS_AUTOCONVERTPCM      0x80000000
#endif
#ifndef AUDCLNT_STREAMFLAGS_SRC_DEFAULT_QUALITY
#define AUDCLNT_STREAMFLAGS_SRC_DEFAULT_QUALITY 0x08000000
#endif

#ifndef VIRTUAL_AUDIO_DEVICE_PROCESS_LOOPBACK
#define VIRTUAL_AUDIO_DEVICE_PROCESS_LOOPBACK L"VAD\\Process_Loopback"

typedef enum {
    AUDIOCLIENT_ACTIVATION_TYPE_DEFAULT = 0,
    AUDIOCLIENT_ACTIVATION_TYPE_PROCESS_LOOPBACK = 1
} AUDIOCLIENT_ACTIVATION_TYPE;

typedef enum {
    PROCESS_LOOPBACK_MODE_INCLUDE_TARGET_PROCESS_TREE = 0,
    PROCESS_LOOPBACK_MODE_EXCLUDE_TARGET_PROCESS_TREE = 1
} PROCESS_LOOPBACK_MODE;

typedef struct {
    DWORD                 TargetProcessId;
    PROCESS_LOOPBACK_MODE ProcessLoopbackMode;
} AUDIOCLIENT_PROCESS_LOOPBACK_PARAMS;

/* One-member union; declared flat so it works in C with or without
 * NONAMELESSUNION. Layout matches the SDK definition. */
typedef struct {
    AUDIOCLIENT_ACTIVATION_TYPE         ActivationType;
    AUDIOCLIENT_PROCESS_LOOPBACK_PARAMS ProcessLoopbackParams;
} AUDIOCLIENT_ACTIVATION_PARAMS;

#define LOOPBACK_PARAMS(p) ((p).ProcessLoopbackParams)
#else
#define LOOPBACK_PARAMS(p) ((p).DUMMYUNIONNAME.ProcessLoopbackParams)
#endif /* VIRTUAL_AUDIO_DEVICE_PROCESS_LOOPBACK */

/* All GUIDs defined locally so we never depend on uuid.lib contents. */
static const CLSID g_CLSID_MMDeviceEnumerator =
    {0xbcde0395,0xe52f,0x467c,{0x8e,0x3d,0xc4,0x57,0x92,0x91,0x69,0x2e}};
static const IID g_IID_IMMDeviceEnumerator =
    {0xa95664d2,0x9614,0x4f35,{0xa7,0x46,0xde,0x8d,0xb6,0x36,0x17,0xe6}};
static const IID g_IID_IAudioClient =
    {0x1cb9ad4c,0xdbfa,0x4c32,{0xb1,0x78,0xc2,0xf5,0x68,0xa7,0x03,0xb2}};
static const IID g_IID_IAudioCaptureClient =
    {0xc8adbd64,0xe71e,0x48a0,{0xa4,0xde,0x18,0x5c,0x39,0x5c,0xd3,0x17}};
static const IID g_IID_IAudioRenderClient =
    {0xf294acfc,0x3146,0x4483,{0xa7,0xbf,0xad,0xdc,0xa7,0xc2,0x60,0xe2}};
static const IID g_IID_IActCompletionHandler =
    {0x41d949ab,0x9862,0x444a,{0x80,0xf6,0xc2,0x61,0x33,0x4d,0xa5,0xeb}};
static const IID g_IID_IAgileObject =
    {0x94ea2b94,0xe9cc,0x49e0,{0xc0,0xff,0xee,0x64,0xca,0x8f,0x5b,0x90}};
static const IID g_IID_IUnknown_ =
    {0x00000000,0x0000,0x0000,{0xc0,0x00,0x00,0x00,0x00,0x00,0x00,0x46}};
static const PROPERTYKEY g_PKEY_Device_FriendlyName =
    {{0xa45c254e,0xdf1c,0x4efd,{0x80,0x20,0x67,0xd1,0x46,0xa8,0x50,0xe0}}, 14};

typedef HRESULT (WINAPI *PFN_ActivateAudioInterfaceAsync)(
    LPCWSTR, REFIID, PROPVARIANT *,
    IActivateAudioInterfaceCompletionHandler *,
    IActivateAudioInterfaceAsyncOperation **);

/* ------------------------------------------------------------------ */
/* Internal mix format: 32-bit float, stereo, 48 kHz                    */
/* ------------------------------------------------------------------ */

#define MIX_RATE      48000
#define MIX_CHANNELS  2
#define RING_SECONDS  2
/* A source is only played once PRIME_MS of it is banked, and it keeps that
 * cushion in hand. Too small a cushion is what makes the tunnel sound like a
 * bad codec: every scheduling hiccup punches a hole of silence into the audio.
 * MAX_LAG_MS then caps how far behind real time the cushion may drift. */
#define PRIME_MS      60
#define MAX_LAG_MS    150   /* backlog tolerated before old audio is dropped */
#define RENDER_BUF_MS 60    /* virtual-cable buffer; also the base latency */

#define CHECK(hr, what)                                                     \
    do {                                                                    \
        if (FAILED(hr)) {                                                   \
            fprintf(stderr, "\n[error] %s failed: 0x%08lX\n",               \
                    (what), (unsigned long)(hr));                           \
            goto fail;                                                      \
        }                                                                   \
    } while (0)

static volatile LONG g_running   = 1;   /* cleared on quit           */
static volatile LONG g_app_on    = 1;   /* 'a' toggles app audio     */
static volatile LONG g_mic_on    = 1;   /* 'm' toggles mic           */
static float         g_app_gain  = 1.0f;
static float         g_mic_gain  = 1.0f;
static volatile LONG g_app_peak_i = 0;  /* peak * 10000, for the meter */
static volatile LONG g_mic_peak_i = 0;

/* Frames each stage has moved. If audio dies, whichever counter stops first
 * names the guilty stage, so the status line reports all three. */
static volatile LONG g_app_frames = 0;
static volatile LONG g_mic_frames = 0;
static volatile LONG g_ren_frames = 0;
static volatile LONG g_restarts   = 0;

/* Warnings scroll away behind the status line, so keep a copy on disk. */
static void tlog(const char *fmt, ...)
{
    static CRITICAL_SECTION cs;
    static int   ready;
    static FILE *fp;
    va_list      ap;
    SYSTEMTIME   st;

    if (!ready) { InitializeCriticalSection(&cs); ready = 1; }
    EnterCriticalSection(&cs);
    if (!fp) fp = fopen("audiotunnel.log", "a");
    GetLocalTime(&st);
    if (fp) fprintf(fp, "%02d:%02d:%02d.%03d  ",
                    st.wHour, st.wMinute, st.wSecond, st.wMilliseconds);
    va_start(ap, fmt);
    if (fp) { vfprintf(fp, fmt, ap); fputc('\n', fp); fflush(fp); }
    va_end(ap);
    va_start(ap, fmt);
    fprintf(stderr, "\n[log] ");
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
    LeaveCriticalSection(&cs);
}

/* ------------------------------------------------------------------ */
/* Ring buffer (frames of MIX_CHANNELS floats)                          */
/* ------------------------------------------------------------------ */

typedef struct {
    float           *data;
    size_t           cap;      /* in frames */
    size_t           r, w;
    size_t           count;    /* frames stored */
    CRITICAL_SECTION cs;
    LONG             dropped;      /* frames thrown away (overflow or trim) */
    LONG             starved;      /* frames of silence faked on underrun   */
    int              primed;       /* render thread only                    */
    size_t           prime_frames;
} Ring;

static int ring_init(Ring *rb, size_t frames)
{
    rb->data = (float *)calloc(frames * MIX_CHANNELS, sizeof(float));
    if (!rb->data) return 0;
    rb->cap = frames;
    rb->r = rb->w = rb->count = 0;
    rb->dropped = 0;
    rb->starved = 0;
    rb->primed  = 0;
    rb->prime_frames = PRIME_MS * MIX_RATE / 1000;
    InitializeCriticalSection(&rb->cs);
    return 1;
}

static void ring_free(Ring *rb)
{
    if (rb->data) { free(rb->data); rb->data = NULL; }
    DeleteCriticalSection(&rb->cs);
}

/* Push frames; if full, drop the oldest audio to stay near real time. */
static void ring_push(Ring *rb, const float *src, size_t frames)
{
    size_t i;
    EnterCriticalSection(&rb->cs);
    for (i = 0; i < frames; i++) {
        rb->data[rb->w * MIX_CHANNELS + 0] = src[i * MIX_CHANNELS + 0];
        rb->data[rb->w * MIX_CHANNELS + 1] = src[i * MIX_CHANNELS + 1];
        rb->w = (rb->w + 1) % rb->cap;
        if (rb->count < rb->cap) {
            rb->count++;
        } else {
            rb->r = (rb->r + 1) % rb->cap;   /* overwrote the oldest frame */
            rb->dropped++;
        }
    }
    LeaveCriticalSection(&rb->cs);
}

/* Pop up to `frames`; anything missing comes out as silence. */
static size_t ring_pop(Ring *rb, float *dst, size_t frames)
{
    size_t i, got;
    EnterCriticalSection(&rb->cs);
    got = rb->count < frames ? rb->count : frames;
    for (i = 0; i < got; i++) {
        dst[i * MIX_CHANNELS + 0] = rb->data[rb->r * MIX_CHANNELS + 0];
        dst[i * MIX_CHANNELS + 1] = rb->data[rb->r * MIX_CHANNELS + 1];
        rb->r = (rb->r + 1) % rb->cap;
    }
    rb->count -= got;
    LeaveCriticalSection(&rb->cs);
    for (i = got; i < frames; i++) {
        dst[i * MIX_CHANNELS + 0] = 0.0f;
        dst[i * MIX_CHANNELS + 1] = 0.0f;
    }
    return got;
}

static size_t ring_fill(Ring *rb);

/* What the mixer pulls through. Silence is emitted until the cushion is built,
 * and a run-dry costs the cushion again rather than being papered over frame by
 * frame -- one clean gap sounds far better than a continuous stutter.
 * Single consumer (the render thread), so `primed` needs no lock. */
static size_t ring_pull(Ring *rb, float *dst, size_t frames)
{
    size_t got;

    if (!rb->primed) {
        if (ring_fill(rb) < rb->prime_frames) {
            memset(dst, 0, frames * MIX_CHANNELS * sizeof(float));
            return 0;
        }
        rb->primed = 1;
    }
    got = ring_pop(rb, dst, frames);
    if (got < frames) {
        rb->primed = 0;
        rb->starved += (LONG)(frames - got);
    }
    return got;
}

/* Throw away anything older than max_frames. Keeps the tunnel from running
 * behind real time: a backlog here is pure added delay on your voice. */
static void ring_trim(Ring *rb, size_t max_frames)
{
    EnterCriticalSection(&rb->cs);
    if (rb->count > max_frames) {
        size_t drop = rb->count - max_frames;
        rb->r = (rb->r + drop) % rb->cap;
        rb->count -= drop;
        rb->dropped += (LONG)drop;
    }
    LeaveCriticalSection(&rb->cs);
}

static size_t ring_fill(Ring *rb)
{
    size_t n;
    EnterCriticalSection(&rb->cs);
    n = rb->count;
    LeaveCriticalSection(&rb->cs);
    return n;
}

/* UTF-16 -> UTF-8 for console output. Rotating scratch buffers so several
 * calls can appear in one printf. */
static const char *u8(const WCHAR *w)
{
    static char bufs[4][512];
    static int  slot;
    char *b = bufs[slot];
    slot = (slot + 1) & 3;
    if (!WideCharToMultiByte(CP_UTF8, 0, w, -1, b, sizeof(bufs[0]), NULL, NULL))
        b[0] = 0;
    return b;
}

/* ------------------------------------------------------------------ */
/* Window / process picking                                             */
/* ------------------------------------------------------------------ */

#define MAX_WINDOWS 256

typedef struct {
    DWORD pid;
    WCHAR title[160];
    WCHAR exe[64];
} WinEntry;

static WinEntry g_wins[MAX_WINDOWS];
static int      g_win_count;

static void process_exe_name(DWORD pid, WCHAR *out, size_t cch)
{
    HANDLE h;
    WCHAR  path[MAX_PATH];
    DWORD  len = MAX_PATH;
    WCHAR *base;

    out[0] = 0;
    h = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
    if (!h) { wcsncpy(out, L"?", cch); return; }
    if (QueryFullProcessImageNameW(h, 0, path, &len)) {
        base = wcsrchr(path, L'\\');
        wcsncpy(out, base ? base + 1 : path, cch - 1);
        out[cch - 1] = 0;
    }
    CloseHandle(h);
}

static BOOL CALLBACK enum_windows_cb(HWND hwnd, LPARAM lp)
{
    DWORD pid = 0;
    int   i, len;
    (void)lp;

    if (g_win_count >= MAX_WINDOWS) return FALSE;
    if (!IsWindowVisible(hwnd)) return TRUE;
    if (GetWindow(hwnd, GW_OWNER) != NULL) return TRUE;
    if (GetWindowLongPtrW(hwnd, GWL_EXSTYLE) & WS_EX_TOOLWINDOW) return TRUE;

    len = GetWindowTextLengthW(hwnd);
    if (len <= 0) return TRUE;

    GetWindowThreadProcessId(hwnd, &pid);
    if (!pid || pid == GetCurrentProcessId()) return TRUE;

    for (i = 0; i < g_win_count; i++)          /* one row per process */
        if (g_wins[i].pid == pid) return TRUE;

    g_wins[g_win_count].pid = pid;
    GetWindowTextW(hwnd, g_wins[g_win_count].title,
                   (int)(sizeof(g_wins[0].title) / sizeof(WCHAR)) - 1);
    process_exe_name(pid, g_wins[g_win_count].exe,
                     sizeof(g_wins[0].exe) / sizeof(WCHAR));
    g_win_count++;
    return TRUE;
}

static void list_windows(void)
{
    int i;
    g_win_count = 0;
    EnumWindows(enum_windows_cb, 0);
    printf("\nWindows with audio-capable processes:\n");
    for (i = 0; i < g_win_count; i++)
        printf("  [%2d] pid %-6lu  %-20s  %s\n", i,
               (unsigned long)g_wins[i].pid, u8(g_wins[i].exe), u8(g_wins[i].title));
}

/* ------------------------------------------------------------------ */
/* Audio endpoint enumeration                                           */
/* ------------------------------------------------------------------ */

#define MAX_DEVICES 64

typedef struct {
    WCHAR id[256];
    WCHAR name[256];
} DevEntry;

static IMMDeviceEnumerator *g_enum;

static int list_devices(EDataFlow flow, DevEntry *out, int max)
{
    IMMDeviceCollection *coll = NULL;
    UINT count = 0, i;
    int n = 0;
    HRESULT hr;

    hr = IMMDeviceEnumerator_EnumAudioEndpoints(g_enum, flow, DEVICE_STATE_ACTIVE, &coll);
    if (FAILED(hr)) return 0;
    IMMDeviceCollection_GetCount(coll, &count);

    for (i = 0; i < count && n < max; i++) {
        IMMDevice      *dev   = NULL;
        IPropertyStore *props = NULL;
        LPWSTR          id    = NULL;
        PROPVARIANT     pv;

        if (FAILED(IMMDeviceCollection_Item(coll, i, &dev))) continue;
        if (SUCCEEDED(IMMDevice_GetId(dev, &id))) {
            wcsncpy(out[n].id, id, 255);
            out[n].id[255] = 0;
            CoTaskMemFree(id);
        }
        wcscpy(out[n].name, L"(unknown)");
        if (SUCCEEDED(IMMDevice_OpenPropertyStore(dev, STGM_READ, &props))) {
            PropVariantInit(&pv);
            if (SUCCEEDED(IPropertyStore_GetValue(props, &g_PKEY_Device_FriendlyName, &pv))
                && pv.vt == VT_LPWSTR) {
                wcsncpy(out[n].name, pv.pwszVal, 255);
                out[n].name[255] = 0;
            }
            PropVariantClear(&pv);
            IPropertyStore_Release(props);
        }
        IMMDevice_Release(dev);
        n++;
    }
    IMMDeviceCollection_Release(coll);
    return n;
}

static void print_devices(const char *header, DevEntry *d, int n)
{
    int i;
    printf("\n%s\n", header);
    for (i = 0; i < n; i++)
        printf("  [%2d] %s\n", i, u8(d[i].name));
}

/* case-insensitive substring match on the friendly name */
static int find_device(DevEntry *d, int n, const char *needle)
{
    WCHAR wneedle[256];
    int   i;
    MultiByteToWideChar(CP_UTF8, 0, needle, -1, wneedle, 256);
    CharLowerW(wneedle);
    for (i = 0; i < n; i++) {
        WCHAR tmp[256];
        wcscpy(tmp, d[i].name);
        CharLowerW(tmp);
        if (wcsstr(tmp, wneedle)) return i;
    }
    return -1;
}

static IMMDevice *device_by_id(const WCHAR *id)
{
    IMMDevice *dev = NULL;
    if (FAILED(IMMDeviceEnumerator_GetDevice(g_enum, (LPWSTR)id, &dev))) return NULL;
    return dev;
}

/* ------------------------------------------------------------------ */
/* Format helpers                                                       */
/* ------------------------------------------------------------------ */

static void make_float_format(WAVEFORMATEX *w)
{
    w->wFormatTag      = WAVE_FORMAT_IEEE_FLOAT;
    w->nChannels       = MIX_CHANNELS;
    w->nSamplesPerSec  = MIX_RATE;
    w->wBitsPerSample  = 32;
    w->nBlockAlign     = (WORD)(w->nChannels * w->wBitsPerSample / 8);
    w->nAvgBytesPerSec = w->nSamplesPerSec * w->nBlockAlign;
    w->cbSize          = 0;
}

static void make_s16_format(WAVEFORMATEX *w)
{
    w->wFormatTag      = WAVE_FORMAT_PCM;
    w->nChannels       = MIX_CHANNELS;
    w->nSamplesPerSec  = MIX_RATE;
    w->wBitsPerSample  = 16;
    w->nBlockAlign     = (WORD)(w->nChannels * w->wBitsPerSample / 8);
    w->nAvgBytesPerSec = w->nSamplesPerSec * w->nBlockAlign;
    w->cbSize          = 0;
}

/* ------------------------------------------------------------------ */
/* IActivateAudioInterfaceCompletionHandler, hand-rolled in C           */
/* ------------------------------------------------------------------ */

typedef struct {
    IActivateAudioInterfaceCompletionHandler iface;   /* must be first */
    LONG      ref;
    HANDLE    done;
    HRESULT   hr;
    IUnknown *result;
} ActHandler;

static HRESULT STDMETHODCALLTYPE AH_QueryInterface(
    IActivateAudioInterfaceCompletionHandler *This, REFIID riid, void **ppv)
{
    if (!ppv) return E_POINTER;
    if (IsEqualGUID(riid, &g_IID_IUnknown_) ||
        IsEqualGUID(riid, &g_IID_IActCompletionHandler) ||
        IsEqualGUID(riid, &g_IID_IAgileObject)) {
        *ppv = This;
        This->lpVtbl->AddRef(This);
        return S_OK;
    }
    *ppv = NULL;
    return E_NOINTERFACE;
}

static ULONG STDMETHODCALLTYPE AH_AddRef(IActivateAudioInterfaceCompletionHandler *This)
{
    ActHandler *h = (ActHandler *)This;
    return (ULONG)InterlockedIncrement(&h->ref);
}

static ULONG STDMETHODCALLTYPE AH_Release(IActivateAudioInterfaceCompletionHandler *This)
{
    ActHandler *h = (ActHandler *)This;
    LONG n = InterlockedDecrement(&h->ref);
    if (n == 0) {
        if (h->done) CloseHandle(h->done);
        free(h);
    }
    return (ULONG)n;
}

static HRESULT STDMETHODCALLTYPE AH_ActivateCompleted(
    IActivateAudioInterfaceCompletionHandler *This,
    IActivateAudioInterfaceAsyncOperation *op)
{
    ActHandler *h = (ActHandler *)This;
    HRESULT     hrActivate = E_FAIL;
    IUnknown   *unk = NULL;
    HRESULT     hr;

    hr = IActivateAudioInterfaceAsyncOperation_GetActivateResult(op, &hrActivate, &unk);
    h->hr     = SUCCEEDED(hr) ? hrActivate : hr;
    h->result = SUCCEEDED(h->hr) ? unk : NULL;
    if (FAILED(h->hr) && unk) IUnknown_Release(unk);
    SetEvent(h->done);
    return S_OK;
}

static IActivateAudioInterfaceCompletionHandlerVtbl g_ah_vtbl = {
    AH_QueryInterface, AH_AddRef, AH_Release, AH_ActivateCompleted
};

/* Activate a per-process loopback IAudioClient for pid (whole process tree). */
static IAudioClient *activate_process_loopback(DWORD pid)
{
    static PFN_ActivateAudioInterfaceAsync pActivate;
    AUDIOCLIENT_ACTIVATION_PARAMS params;
    PROPVARIANT                   pv;
    ActHandler                   *h  = NULL;
    IActivateAudioInterfaceAsyncOperation *op = NULL;
    IAudioClient                 *client = NULL;
    HRESULT hr;

    if (!pActivate) {
        HMODULE m = LoadLibraryW(L"Mmdevapi.dll");
        if (m) pActivate = (PFN_ActivateAudioInterfaceAsync)
                   GetProcAddress(m, "ActivateAudioInterfaceAsync");
        if (!pActivate) {
            fprintf(stderr, "[error] ActivateAudioInterfaceAsync unavailable "
                            "(needs Windows 10 build 20348 or newer)\n");
            return NULL;
        }
    }

    ZeroMemory(&params, sizeof(params));
    params.ActivationType = AUDIOCLIENT_ACTIVATION_TYPE_PROCESS_LOOPBACK;
    LOOPBACK_PARAMS(params).TargetProcessId     = pid;
    LOOPBACK_PARAMS(params).ProcessLoopbackMode =
        PROCESS_LOOPBACK_MODE_INCLUDE_TARGET_PROCESS_TREE;

    PropVariantInit(&pv);
    pv.vt              = VT_BLOB;
    pv.blob.cbSize     = sizeof(params);
    pv.blob.pBlobData  = (BYTE *)&params;

    h = (ActHandler *)calloc(1, sizeof(ActHandler));
    if (!h) return NULL;
    h->iface.lpVtbl = &g_ah_vtbl;
    h->ref          = 1;
    h->done         = CreateEventW(NULL, FALSE, FALSE, NULL);

    hr = pActivate(VIRTUAL_AUDIO_DEVICE_PROCESS_LOOPBACK, &g_IID_IAudioClient,
                   &pv, &h->iface, &op);
    if (FAILED(hr)) {
        fprintf(stderr, "[error] ActivateAudioInterfaceAsync: 0x%08lX\n",
                (unsigned long)hr);
        goto done;
    }
    if (WaitForSingleObject(h->done, 5000) != WAIT_OBJECT_0) {
        fprintf(stderr, "[error] activation timed out\n");
        goto done;
    }
    if (FAILED(h->hr)) {
        fprintf(stderr, "[error] process loopback activation: 0x%08lX\n",
                (unsigned long)h->hr);
        goto done;
    }
    client = (IAudioClient *)h->result;   /* riid was IID_IAudioClient */

done:
    if (op) IActivateAudioInterfaceAsyncOperation_Release(op);
    h->iface.lpVtbl->Release(&h->iface);
    return client;
}

/* ------------------------------------------------------------------ */
/* Capture threads                                                      */
/* ------------------------------------------------------------------ */

typedef struct {
    IAudioClient        *client;
    IAudioCaptureClient *capture;
    HANDLE               evt;
    Ring                *ring;
    int                  is_float;   /* stream is float32, else int16 */
    volatile LONG       *peak_out;
    volatile LONG       *frames_out;
    const char          *label;
    /* Everything needed to build this stream again after it wedges. */
    IMMDevice           *dev;        /* mic only  */
    DWORD                pid;        /* app only  */
    int                  is_app;
    DWORD                stall_ms;   /* no frames at all tolerated, ms */
    DWORD                silence_ms; /* frames but no signal tolerated, ms (0 = never) */
    DWORD                last_signal;
    /* Per-thread staging buffer. Must NOT be shared: both capture threads
     * run this same code at the same time. */
    float                scratch[4096 * MIX_CHANNELS];
} CaptureCtx;

static int open_mic(IMMDevice *dev, CaptureCtx *c);
static int open_app_loopback(DWORD pid, CaptureCtx *c);

static void close_capture(CaptureCtx *c)
{
    if (c->capture) { IAudioCaptureClient_Release(c->capture); c->capture = NULL; }
    if (c->client)  { IAudioClient_Stop(c->client);
                      IAudioClient_Release(c->client);  c->client = NULL; }
    if (c->evt)     { CloseHandle(c->evt); c->evt = NULL; }
}

/* Two levels of repair: nudge the stream, and if that will not do, throw the
 * whole client away and activate a new one. */
static int restart_capture(CaptureCtx *c, int full)
{
    HRESULT hr;

    InterlockedIncrement(&g_restarts);
    if (!full && c->client) {
        IAudioClient_Stop(c->client);
        IAudioClient_Reset(c->client);
        hr = IAudioClient_Start(c->client);
        if (SUCCEEDED(hr)) { tlog("%s stream restarted", c->label); return 1; }
        tlog("%s restart failed: 0x%08lX -- reopening", c->label, (unsigned long)hr);
    }

    close_capture(c);
    if (c->is_app ? !open_app_loopback(c->pid, c) : !open_mic(c->dev, c)) {
        tlog("%s reopen FAILED", c->label);
        return 0;
    }
    hr = IAudioClient_Start(c->client);
    if (FAILED(hr)) {
        tlog("%s start after reopen failed: 0x%08lX", c->label, (unsigned long)hr);
        return 0;
    }
    tlog("%s reopened", c->label);
    return 1;
}

/* Convert one packet into the internal float/stereo layout and enqueue it. */
static void push_packet(CaptureCtx *c, const BYTE *data, UINT32 frames, DWORD flags)
{
    float *scratch = c->scratch;
    UINT32 done = 0;
    float  peak = 0.0f;

    while (done < frames) {
        UINT32 chunk = frames - done;
        UINT32 i;
        if (chunk > 4096) chunk = 4096;

        if (flags & AUDCLNT_BUFFERFLAGS_SILENT) {
            memset(scratch, 0, chunk * MIX_CHANNELS * sizeof(float));
        } else if (c->is_float) {
            const float *src = (const float *)data + (size_t)done * MIX_CHANNELS;
            for (i = 0; i < chunk * MIX_CHANNELS; i++) {
                float v = src[i];
                scratch[i] = v;
                if (v < 0) v = -v;
                if (v > peak) peak = v;
            }
        } else {
            const short *src = (const short *)data + (size_t)done * MIX_CHANNELS;
            for (i = 0; i < chunk * MIX_CHANNELS; i++) {
                float v = src[i] * (1.0f / 32768.0f);
                scratch[i] = v;
                if (v < 0) v = -v;
                if (v > peak) peak = v;
            }
        }
        ring_push(c->ring, scratch, chunk);
        done += chunk;
    }
    InterlockedExchange(c->peak_out, (LONG)(peak * 10000.0f));
    InterlockedExchangeAdd(c->frames_out, (LONG)frames);
    if (peak > 0.0005f) c->last_signal = GetTickCount();
}

static DWORD WINAPI capture_thread(LPVOID arg)
{
    CaptureCtx *c = (CaptureCtx *)arg;
    HRESULT     hr;
    DWORD       last_data;
    DWORD       sil_wait;
    int         stalls = 0;

    CoInitializeEx(NULL, COINIT_MULTITHREADED);
    hr = IAudioClient_Start(c->client);
    if (FAILED(hr)) {
        tlog("%s Start: 0x%08lX", c->label, (unsigned long)hr);
        return 1;
    }

    last_data      = GetTickCount();
    c->last_signal = last_data;
    sil_wait       = c->silence_ms ? c->silence_ms : 0xFFFFFFFFu;

    while (InterlockedCompareExchange(&g_running, 1, 1)) {
        UINT32 packet = 0;
        int    got_any = 0;
        DWORD  now;

        /* Timeout instead of an infinite wait: a silent app may not signal. */
        WaitForSingleObject(c->evt, 100);

        for (;;) {
            BYTE  *data  = NULL;
            UINT32 avail = 0;
            DWORD  flags = 0;

            hr = IAudioCaptureClient_GetNextPacketSize(c->capture, &packet);
            if (FAILED(hr)) {
                tlog("%s GetNextPacketSize: 0x%08lX", c->label, (unsigned long)hr);
                if (!restart_capture(c, hr != AUDCLNT_E_DEVICE_INVALIDATED)) goto out;
                break;
            }
            if (packet == 0) break;

            hr = IAudioCaptureClient_GetBuffer(c->capture, &data, &avail, &flags, NULL, NULL);
            if (hr == AUDCLNT_S_BUFFER_EMPTY) break;
            if (FAILED(hr)) {
                tlog("%s GetBuffer: 0x%08lX", c->label, (unsigned long)hr);
                if (!restart_capture(c, hr != AUDCLNT_E_DEVICE_INVALIDATED)) goto out;
                break;
            }
            push_packet(c, data, avail, flags);
            IAudioCaptureClient_ReleaseBuffer(c->capture, avail);
            if (avail) got_any = 1;
        }

        /* Watchdog. A WASAPI stream can go quiet without ever reporting an
         * error -- the classic way audio "just stops" after a while. If no
         * frames arrive for stall_ms, put the stream back on its feet. */
        now = GetTickCount();

        /* Frames keep arriving but every one of them is silent. A loopback
         * stream that has quietly detached from its target looks exactly like
         * this, and no error is ever reported -- so re-activate it. While the
         * app really is silent this costs nothing audible, and the wait backs
         * off so a long quiet stretch does not thrash. */
        if (c->silence_ms && now - c->last_signal > sil_wait) {
            tlog("%s frames flowing but silent for %lu ms -- reactivating",
                 c->label, (unsigned long)(now - c->last_signal));
            c->last_signal = now;
            last_data      = now;
            sil_wait       = sil_wait < 60000 ? sil_wait * 2 : 60000;
            if (!restart_capture(c, 1)) goto out;
            continue;
        }
        if (InterlockedCompareExchange(c->peak_out, 0, 0) > 5) sil_wait = c->silence_ms;

        if (got_any) {
            last_data = now;
            stalls    = 0;
        } else if (now - last_data > c->stall_ms) {
            /* First try the cheap nudge; if the stream is still dead next time
             * round, the client itself is stale, so build a new one. */
            stalls++;
            tlog("%s delivered nothing for %lu ms (stall #%d) -- restarting",
                 c->label, (unsigned long)(now - last_data), stalls);
            last_data = now;
            if (!restart_capture(c, stalls > 1)) goto out;
        }
    }
out:
    if (c->client) IAudioClient_Stop(c->client);
    CoUninitialize();
    return 0;
}

/* The endpoint's own shared-mode format. Everything we send is converted to
 * this, so a cable stuck at 16-bit/44.1 kHz is heard as "low bitrate". */
static void report_mix_format(IAudioClient *client, const char *label)
{
    WAVEFORMATEX *mix = NULL;

    if (!client || FAILED(IAudioClient_GetMixFormat(client, &mix)) || !mix) return;
    printf("  %-5s: endpoint runs at %lu Hz, %u ch, %u-bit\n",
           label, (unsigned long)mix->nSamplesPerSec,
           (unsigned)mix->nChannels, (unsigned)mix->wBitsPerSample);
    CoTaskMemFree(mix);
}

/* Set up a normal WASAPI capture endpoint (your real microphone). */
static int open_mic(IMMDevice *dev, CaptureCtx *c)
{
    WAVEFORMATEX fmt;
    HRESULT      hr;
    DWORD        flags = AUDCLNT_STREAMFLAGS_EVENTCALLBACK |
                         AUDCLNT_STREAMFLAGS_AUTOCONVERTPCM |
                         AUDCLNT_STREAMFLAGS_SRC_DEFAULT_QUALITY;

    hr = IMMDevice_Activate(dev, &g_IID_IAudioClient, CLSCTX_ALL, NULL,
                            (void **)&c->client);
    if (FAILED(hr)) { fprintf(stderr, "[error] mic Activate: 0x%08lX\n",
                              (unsigned long)hr); return 0; }

    make_float_format(&fmt);
    c->is_float = 1;
    hr = IAudioClient_Initialize(c->client, AUDCLNT_SHAREMODE_SHARED, flags,
                                 2000000, 0, &fmt, NULL);
    if (FAILED(hr)) {
        make_s16_format(&fmt);
        c->is_float = 0;
        hr = IAudioClient_Initialize(c->client, AUDCLNT_SHAREMODE_SHARED, flags,
                                     2000000, 0, &fmt, NULL);
    }
    if (FAILED(hr)) { fprintf(stderr, "[error] mic Initialize: 0x%08lX\n",
                              (unsigned long)hr); return 0; }

    c->evt = CreateEventW(NULL, FALSE, FALSE, NULL);
    IAudioClient_SetEventHandle(c->client, c->evt);
    hr = IAudioClient_GetService(c->client, &g_IID_IAudioCaptureClient,
                                 (void **)&c->capture);
    if (FAILED(hr)) { fprintf(stderr, "[error] mic GetService: 0x%08lX\n",
                              (unsigned long)hr); return 0; }
    return 1;
}

/* Set up the per-process loopback capture for the chosen app. */
static int open_app_loopback(DWORD pid, CaptureCtx *c)
{
    WAVEFORMATEX fmt;
    HRESULT      hr;
    DWORD        flags = AUDCLNT_STREAMFLAGS_LOOPBACK |
                         AUDCLNT_STREAMFLAGS_EVENTCALLBACK |
                         AUDCLNT_STREAMFLAGS_AUTOCONVERTPCM |
                         AUDCLNT_STREAMFLAGS_SRC_DEFAULT_QUALITY;

    c->client = activate_process_loopback(pid);
    if (!c->client) return 0;

    make_float_format(&fmt);
    c->is_float = 1;
    hr = IAudioClient_Initialize(c->client, AUDCLNT_SHAREMODE_SHARED, flags,
                                 2000000, 0, &fmt, NULL);
    if (FAILED(hr)) {
        make_s16_format(&fmt);
        c->is_float = 0;
        hr = IAudioClient_Initialize(c->client, AUDCLNT_SHAREMODE_SHARED, flags,
                                     2000000, 0, &fmt, NULL);
    }
    if (FAILED(hr)) { fprintf(stderr, "[error] loopback Initialize: 0x%08lX\n",
                              (unsigned long)hr); return 0; }

    c->evt = CreateEventW(NULL, FALSE, FALSE, NULL);
    IAudioClient_SetEventHandle(c->client, c->evt);
    hr = IAudioClient_GetService(c->client, &g_IID_IAudioCaptureClient,
                                 (void **)&c->capture);
    if (FAILED(hr)) { fprintf(stderr, "[error] loopback GetService: 0x%08lX\n",
                              (unsigned long)hr); return 0; }
    return 1;
}

/* ------------------------------------------------------------------ */
/* Render thread: mix both rings into the virtual cable                 */
/* ------------------------------------------------------------------ */

typedef struct {
    IAudioClient       *client;
    IAudioRenderClient *render;
    HANDLE              evt;
    UINT32              buffer_frames;
    int                 is_float;
    Ring               *app;
    Ring               *mic;
    IMMDevice          *dev;
} RenderCtx;

static int open_render(IMMDevice *dev, RenderCtx *r);

static void close_render(RenderCtx *r)
{
    if (r->render) { IAudioRenderClient_Release(r->render); r->render = NULL; }
    if (r->client) { IAudioClient_Stop(r->client);
                     IAudioClient_Release(r->client); r->client = NULL; }
    if (r->evt)    { CloseHandle(r->evt); r->evt = NULL; }
}

static int restart_render(RenderCtx *r, int full)
{
    HRESULT hr;

    InterlockedIncrement(&g_restarts);
    if (!full && r->client) {
        IAudioClient_Stop(r->client);
        IAudioClient_Reset(r->client);
        hr = IAudioClient_Start(r->client);
        if (SUCCEEDED(hr)) { tlog("render stream restarted"); return 1; }
        tlog("render restart failed: 0x%08lX -- reopening", (unsigned long)hr);
    }

    close_render(r);
    if (!open_render(r->dev, r)) { tlog("render reopen FAILED"); return 0; }
    hr = IAudioClient_Start(r->client);
    if (FAILED(hr)) {
        tlog("render start after reopen failed: 0x%08lX", (unsigned long)hr);
        return 0;
    }
    tlog("render reopened");
    return 1;
}

static DWORD WINAPI render_thread(LPVOID arg)
{
    RenderCtx *r = (RenderCtx *)arg;
    static float a[4096 * MIX_CHANNELS];
    static float m[4096 * MIX_CHANNELS];
    HRESULT hr;
    DWORD   last_write;

    CoInitializeEx(NULL, COINIT_MULTITHREADED);
    hr = IAudioClient_Start(r->client);
    if (FAILED(hr)) {
        tlog("render Start: 0x%08lX", (unsigned long)hr);
        return 1;
    }
    last_write = GetTickCount();

    while (InterlockedCompareExchange(&g_running, 1, 1)) {
        UINT32 padding = 0, want;
        BYTE  *out = NULL;
        UINT32 i;
        float  ag, mg;

        WaitForSingleObject(r->evt, 100);

        hr = IAudioClient_GetCurrentPadding(r->client, &padding);
        if (FAILED(hr)) {
            tlog("render GetCurrentPadding: 0x%08lX", (unsigned long)hr);
            if (!restart_render(r, hr != AUDCLNT_E_DEVICE_INVALIDATED)) break;
            last_write = GetTickCount();
            continue;
        }
        want = r->buffer_frames - padding;
        if (want > 4096) want = 4096;
        if (want == 0) {
            /* The endpoint has stopped draining what we wrote. Left alone this
             * is exactly the "audio dies after a while" symptom. */
            if (GetTickCount() - last_write > 1000) {
                tlog("render buffer stuck full for 1s -- restarting");
                if (!restart_render(r, 1)) break;
                last_write = GetTickCount();
            }
            continue;
        }

        hr = IAudioRenderClient_GetBuffer(r->render, want, &out);
        if (FAILED(hr)) {
            tlog("render GetBuffer(%u): 0x%08lX", (unsigned)want, (unsigned long)hr);
            if (!restart_render(r, hr != AUDCLNT_E_DEVICE_INVALIDATED)) break;
            last_write = GetTickCount();
            continue;
        }
        last_write = GetTickCount();

        /* Never let a source run more than MAX_LAG_MS behind the mixer. */
        ring_trim(r->app, want + MAX_LAG_MS * MIX_RATE / 1000);
        ring_trim(r->mic, want + MAX_LAG_MS * MIX_RATE / 1000);

        ring_pull(r->app, a, want);
        ring_pull(r->mic, m, want);

        ag = InterlockedCompareExchange(&g_app_on, 1, 1) ? g_app_gain : 0.0f;
        mg = InterlockedCompareExchange(&g_mic_on, 1, 1) ? g_mic_gain : 0.0f;

        if (r->is_float) {
            float *dst = (float *)out;
            for (i = 0; i < want * MIX_CHANNELS; i++) {
                float v = a[i] * ag + m[i] * mg;
                if (v >  1.0f) v =  1.0f;
                if (v < -1.0f) v = -1.0f;
                dst[i] = v;
            }
        } else {
            short *dst = (short *)out;
            for (i = 0; i < want * MIX_CHANNELS; i++) {
                float v = a[i] * ag + m[i] * mg;
                if (v >  1.0f) v =  1.0f;
                if (v < -1.0f) v = -1.0f;
                dst[i] = (short)(v * 32767.0f);
            }
        }
        IAudioRenderClient_ReleaseBuffer(r->render, want, 0);
        InterlockedExchangeAdd(&g_ren_frames, (LONG)want);
    }

    tlog("render thread exiting");
    if (r->client) IAudioClient_Stop(r->client);
    CoUninitialize();
    return 0;
}

static int open_render(IMMDevice *dev, RenderCtx *r)
{
    WAVEFORMATEX fmt;
    HRESULT      hr;
    DWORD        flags = AUDCLNT_STREAMFLAGS_EVENTCALLBACK |
                         AUDCLNT_STREAMFLAGS_AUTOCONVERTPCM |
                         AUDCLNT_STREAMFLAGS_SRC_DEFAULT_QUALITY;

    hr = IMMDevice_Activate(dev, &g_IID_IAudioClient, CLSCTX_ALL, NULL,
                            (void **)&r->client);
    if (FAILED(hr)) { fprintf(stderr, "[error] render Activate: 0x%08lX\n",
                              (unsigned long)hr); return 0; }

    make_float_format(&fmt);
    r->is_float = 1;
    hr = IAudioClient_Initialize(r->client, AUDCLNT_SHAREMODE_SHARED, flags,
                                 RENDER_BUF_MS * 10000, 0, &fmt, NULL);
    if (FAILED(hr)) {
        make_s16_format(&fmt);
        r->is_float = 0;
        hr = IAudioClient_Initialize(r->client, AUDCLNT_SHAREMODE_SHARED, flags,
                                     1000000, 0, &fmt, NULL);
    }
    if (FAILED(hr)) { fprintf(stderr, "[error] render Initialize: 0x%08lX\n",
                              (unsigned long)hr); return 0; }

    r->evt = CreateEventW(NULL, FALSE, FALSE, NULL);
    IAudioClient_SetEventHandle(r->client, r->evt);
    IAudioClient_GetBufferSize(r->client, &r->buffer_frames);
    hr = IAudioClient_GetService(r->client, &g_IID_IAudioRenderClient,
                                 (void **)&r->render);
    if (FAILED(hr)) { fprintf(stderr, "[error] render GetService: 0x%08lX\n",
                              (unsigned long)hr); return 0; }
    return 1;
}

/* ------------------------------------------------------------------ */
/* main                                                                 */
/* ------------------------------------------------------------------ */

static BOOL WINAPI ctrl_handler(DWORD type)
{
    (void)type;
    InterlockedExchange(&g_running, 0);
    return TRUE;
}

static int prompt_index(const char *what, int count)
{
    char line[64];
    long v;
    for (;;) {
        printf("\nSelect %s [0-%d]: ", what, count - 1);
        fflush(stdout);
        if (!fgets(line, sizeof(line), stdin)) return -1;
        v = strtol(line, NULL, 10);
        if (v >= 0 && v < count) return (int)v;
        printf("  ...not a valid index.\n");
    }
}

/* 20 cells spanning -60 dBFS .. 0 dBFS, so quiet-but-live signals still show. */
static void meter(char *dst, float peak)
{
    int   i, n;
    float db = peak > 1e-6f ? 20.0f * (float)log10(peak) : -120.0f;
    n = (int)((db + 60.0f) / 3.0f + 0.5f);
    if (n < 0)  n = 0;
    if (n > 20) n = 20;
    for (i = 0; i < 20; i++) dst[i] = i < n ? '#' : '.';
    dst[20] = 0;
}

static void usage(void)
{
    printf(
    "audiotunnel -- send an app's audio (plus your mic) into a virtual microphone\n"
    "\n"
    "Usage: audiotunnel.exe [options]\n"
    "  --list             list windows and audio devices, then exit\n"
    "  --pid <n>          capture this process id (and its child processes)\n"
    "  --app <text>       pick the process whose exe/title contains <text>\n"
    "  --out <text>       output device name substring (default: auto-detect CABLE)\n"
    "  --mic <text>       microphone name substring (default: system default mic)\n"
    "  --no-mic           app audio only, do not mix your microphone\n"
    "  --dry-run          capture and show levels only, open no output device\n"
    "  --app-gain <f>     app volume multiplier (default 1.0)\n"
    "  --mic-gain <f>     mic volume multiplier (default 1.0)\n"
    "\n"
    "While running:  a = toggle app audio   m = toggle mic   q = quit\n");
}

int main(int argc, char **argv)
{
    DevEntry    outs[MAX_DEVICES], mics[MAX_DEVICES];
    int         n_outs = 0, n_mics = 0;
    int         out_idx = -1, mic_idx = -1;
    DWORD       pid = 0;
    int         use_mic = 1, do_list = 0, dry_run = 0, i;
    const char *arg_app = NULL, *arg_out = NULL, *arg_mic = NULL;
    IMMDevice  *out_dev = NULL, *mic_dev = NULL;
    Ring        app_ring, mic_ring;
    static CaptureCtx app_ctx, mic_ctx;   /* static: each holds a 32 KB buffer */
    static RenderCtx  ren_ctx;
    HANDLE      th_app = NULL, th_mic = NULL, th_ren = NULL;
    HRESULT     hr;

    ZeroMemory(&app_ctx, sizeof(app_ctx));
    ZeroMemory(&mic_ctx, sizeof(mic_ctx));
    ZeroMemory(&ren_ctx, sizeof(ren_ctx));
    ZeroMemory(&app_ring, sizeof(app_ring));
    ZeroMemory(&mic_ring, sizeof(mic_ring));

    for (i = 1; i < argc; i++) {
        if      (!strcmp(argv[i], "--list"))   do_list = 1;
        else if (!strcmp(argv[i], "--no-mic")) use_mic = 0;
        else if (!strcmp(argv[i], "--dry-run")) dry_run = 1;
        else if (!strcmp(argv[i], "--pid") && i + 1 < argc) pid = (DWORD)strtoul(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--app") && i + 1 < argc) arg_app = argv[++i];
        else if (!strcmp(argv[i], "--out") && i + 1 < argc) arg_out = argv[++i];
        else if (!strcmp(argv[i], "--mic") && i + 1 < argc) arg_mic = argv[++i];
        else if (!strcmp(argv[i], "--app-gain") && i + 1 < argc) g_app_gain = (float)atof(argv[++i]);
        else if (!strcmp(argv[i], "--mic-gain") && i + 1 < argc) g_mic_gain = (float)atof(argv[++i]);
        else { usage(); return 1; }
    }

    SetConsoleOutputCP(CP_UTF8);
    SetConsoleCtrlHandler(ctrl_handler, TRUE);

    hr = CoInitializeEx(NULL, COINIT_MULTITHREADED);
    CHECK(hr, "CoInitializeEx");
    hr = CoCreateInstance(&g_CLSID_MMDeviceEnumerator, NULL, CLSCTX_ALL,
                          &g_IID_IMMDeviceEnumerator, (void **)&g_enum);
    CHECK(hr, "CoCreateInstance(MMDeviceEnumerator)");

    n_outs = list_devices(eRender,  outs, MAX_DEVICES);
    n_mics = list_devices(eCapture, mics, MAX_DEVICES);

    if (do_list) {
        list_windows();
        print_devices("Playback devices (output / virtual cable input):", outs, n_outs);
        print_devices("Recording devices (your real microphone):", mics, n_mics);
        goto fail;
    }

    /* ---- which process ---- */
    if (!pid) {
        g_win_count = 0;
        EnumWindows(enum_windows_cb, 0);
        if (arg_app) {
            WCHAR w[128];
            MultiByteToWideChar(CP_UTF8, 0, arg_app, -1, w, 128);
            CharLowerW(w);
            for (i = 0; i < g_win_count; i++) {
                WCHAR t[256], e[64];
                wcscpy(t, g_wins[i].title); CharLowerW(t);
                wcscpy(e, g_wins[i].exe);   CharLowerW(e);
                if (wcsstr(t, w) || wcsstr(e, w)) { pid = g_wins[i].pid; break; }
            }
            if (!pid) {
                fprintf(stderr, "[error] no window matches '%s'\n", arg_app);
                goto fail;
            }
        } else {
            list_windows();
            i = prompt_index("the app to capture", g_win_count);
            if (i < 0) goto fail;
            pid = g_wins[i].pid;
        }
    }

    /* ---- output device (the virtual cable) ---- */
    if (dry_run) {
        out_idx = -1;
    } else if (arg_out) {
        out_idx = find_device(outs, n_outs, arg_out);
        if (out_idx < 0) {
            fprintf(stderr, "[error] no output device matches '%s'\n", arg_out);
            goto fail;
        }
    } else {
        out_idx = find_device(outs, n_outs, "CABLE Input");
        if (out_idx < 0) out_idx = find_device(outs, n_outs, "VoiceMeeter Input");
        if (out_idx < 0) out_idx = find_device(outs, n_outs, "Virtual");
        if (out_idx < 0) {
            printf("\nNo virtual audio cable found. Install VB-CABLE (free) and pick its\n"
                   "playback side here; WhatsApp then uses the matching recording side.\n");
            print_devices("Playback devices:", outs, n_outs);
            out_idx = prompt_index("the output device", n_outs);
            if (out_idx < 0) goto fail;
        }
    }

    /* ---- microphone ---- */
    if (use_mic) {
        if (arg_mic) {
            mic_idx = find_device(mics, n_mics, arg_mic);
            if (mic_idx < 0) {
                fprintf(stderr, "[error] no microphone matches '%s'\n", arg_mic);
                goto fail;
            }
            mic_dev = device_by_id(mics[mic_idx].id);
        } else {
            hr = IMMDeviceEnumerator_GetDefaultAudioEndpoint(g_enum, eCapture,
                                                             eCommunications, &mic_dev);
            if (FAILED(hr)) {
                printf("\n[warn] no default microphone; continuing without mic\n");
                use_mic = 0;
            }
        }
    }

    if (!dry_run) {
        out_dev = device_by_id(outs[out_idx].id);
        if (!out_dev) {
            fprintf(stderr, "[error] cannot open output device\n");
            goto fail;
        }
    }

    if (!ring_init(&app_ring, MIX_RATE * RING_SECONDS) ||
        !ring_init(&mic_ring, MIX_RATE * RING_SECONDS)) {
        fprintf(stderr, "[error] out of memory\n");
        goto fail;
    }

    /* ---- open the three streams ---- */
    app_ctx.ring = &app_ring;
    app_ctx.peak_out = &g_app_peak_i;
    app_ctx.frames_out = &g_app_frames;
    app_ctx.label = "app";
    app_ctx.is_app = 1;
    app_ctx.pid = pid;
    /* An app that is genuinely silent sends nothing, so be patient here. */
    app_ctx.stall_ms = 3000;
    app_ctx.silence_ms = 5000;
    if (!open_app_loopback(pid, &app_ctx)) goto fail;

    if (use_mic) {
        mic_ctx.ring = &mic_ring;
        mic_ctx.peak_out = &g_mic_peak_i;
        mic_ctx.frames_out = &g_mic_frames;
        mic_ctx.label = "mic";
        mic_ctx.dev = mic_dev;
        mic_ctx.stall_ms = 1500;     /* a live mic always sends something */
        if (!open_mic(mic_dev, &mic_ctx)) {
            printf("[warn] microphone unavailable; continuing with app audio only\n");
            use_mic = 0;
        }
    }

    ren_ctx.app = &app_ring;
    ren_ctx.mic = &mic_ring;
    ren_ctx.dev = out_dev;
    if (!dry_run && !open_render(out_dev, &ren_ctx)) goto fail;

    printf("\n");
    report_mix_format(app_ctx.client, "app");
    if (use_mic)  report_mix_format(mic_ctx.client, "mic");
    if (!dry_run) report_mix_format(ren_ctx.client, "out");

    printf("\n  app  : pid %lu (whole process tree)\n", (unsigned long)pid);
    if (use_mic && mic_idx >= 0) printf("  mic  : %s\n", u8(mics[mic_idx].name));
    else if (use_mic)            printf("  mic  : default communications microphone\n");
    else                         printf("  mic  : (disabled)\n");
    printf("  out  : %s\n", dry_run ? "(dry run, nothing rendered)"
                                    : u8(outs[out_idx].name));
    printf("\nPoint WhatsApp's microphone at the cable's recording side "
           "(e.g. \"CABLE Output\").\n"
           "Keys:  a = app on/off   m = mic on/off   q = quit\n\n");

    th_app = CreateThread(NULL, 0, capture_thread, &app_ctx, 0, NULL);
    if (use_mic) th_mic = CreateThread(NULL, 0, capture_thread, &mic_ctx, 0, NULL);
    if (!dry_run) th_ren = CreateThread(NULL, 0, render_thread, &ren_ctx, 0, NULL);

    while (InterlockedCompareExchange(&g_running, 1, 1)) {
        char am[24], mm[24];
        if (dry_run) {                       /* nobody consumes the rings */
            static float sink[4800 * MIX_CHANNELS];
            while (ring_fill(&app_ring) > 4800) ring_pop(&app_ring, sink, 4800);
            while (ring_fill(&mic_ring) > 4800) ring_pop(&mic_ring, sink, 4800);
        }
        if (_kbhit()) {
            int ch = _getch();
            if      (ch == 'q' || ch == 'Q') InterlockedExchange(&g_running, 0);
            else if (ch == 'a' || ch == 'A') InterlockedExchange(&g_app_on, !g_app_on);
            else if (ch == 'm' || ch == 'M') InterlockedExchange(&g_mic_on, !g_mic_on);
        }
        meter(am, InterlockedCompareExchange(&g_app_peak_i, 0, 0) / 10000.0f);
        meter(mm, InterlockedCompareExchange(&g_mic_peak_i, 0, 0) / 10000.0f);
        /* gap = ms of audio lost to underrun or overflow on each source. A
         * number that keeps climbing is exactly what "sounds like a bad
         * codec"; rst counts stream restarts. */
        printf("\r app[%s]%s mic[%s]%s buf %3u/%3u ms  gap %lu/%lu ms  rst %ld   ",
               am, g_app_on ? " " : "M",
               mm, g_mic_on ? " " : "M",
               (unsigned)(ring_fill(&app_ring) * 1000 / MIX_RATE),
               (unsigned)(ring_fill(&mic_ring) * 1000 / MIX_RATE),
               (unsigned long)((app_ring.starved + app_ring.dropped) * 1000 / MIX_RATE),
               (unsigned long)((mic_ring.starved + mic_ring.dropped) * 1000 / MIX_RATE),
               (long)InterlockedCompareExchange(&g_restarts, 0, 0));
        fflush(stdout);
        Sleep(80);
    }

    printf("\nstopping...\n");
    if (th_app) { WaitForSingleObject(th_app, 2000); CloseHandle(th_app); }
    if (th_mic) { WaitForSingleObject(th_mic, 2000); CloseHandle(th_mic); }
    if (th_ren) { WaitForSingleObject(th_ren, 2000); CloseHandle(th_ren); }

fail:
    if (app_ctx.capture) IAudioCaptureClient_Release(app_ctx.capture);
    if (app_ctx.client)  IAudioClient_Release(app_ctx.client);
    if (app_ctx.evt)     CloseHandle(app_ctx.evt);
    if (mic_ctx.capture) IAudioCaptureClient_Release(mic_ctx.capture);
    if (mic_ctx.client)  IAudioClient_Release(mic_ctx.client);
    if (mic_ctx.evt)     CloseHandle(mic_ctx.evt);
    if (ren_ctx.render)  IAudioRenderClient_Release(ren_ctx.render);
    if (ren_ctx.client)  IAudioClient_Release(ren_ctx.client);
    if (ren_ctx.evt)     CloseHandle(ren_ctx.evt);
    if (out_dev)         IMMDevice_Release(out_dev);
    if (mic_dev)         IMMDevice_Release(mic_dev);
    if (app_ring.data)   ring_free(&app_ring);
    if (mic_ring.data)   ring_free(&mic_ring);
    if (g_enum)          IMMDeviceEnumerator_Release(g_enum);
    CoUninitialize();
    return 0;
}
