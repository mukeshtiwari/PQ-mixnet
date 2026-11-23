// mixnative.cpp -- native provers and verifiers for the BGV proof of shuffle and the proof of
// partial decryption. Same protocols, Fiat-Shamir transcripts and byte formats as mix_proof.py and
// dec_proof.py (the Python references), so each implementation can verify the other's proofs.
//
// Build:  g++ -O3 -march=native -std=c++20 -Wno-deprecated-declarations mixnative.cpp -lcrypto -o mixnative
// Usage:  mixnative selftest | mixnative checkC
//         mixnative prove  N tau C1 C2 qbits seed [prefix|-] [store]   (generates an instance, proves, verifies;
//                          prefix: write prefix.inst / prefix.proof;  store: keep the encoded matrix instead of re-encoding)
//         mixnative verify N tau C1 C2 qbits inst.bin proof.bin
//         mixnative decprove  N tau base kdig C1 C2 qbits seed [prefix|-] [generic]   (decryption proof, as dec_proof.py;
//                          C1, C2 = 0: the defaults of DecParams; prefix: write prefix.stmt / prefix.proof)
//         mixnative decverify N tau base kdig C1 C2 qbits stmt.bin proof.bin
//         mixnative checkG    (specialised vs generic digit sumcheck)
//
// The committed matrix is never stored: rows are encoded one at a time and hashed into
// per-column running hashes; the opened columns are recomputed in a second pass.
// NOTE: benchmark code.  Prover randomness comes from a fast non-cryptographic generator.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <vector>
#include <array>
#include <string>
#include <map>
#include <set>
#include <algorithm>
#include <chrono>
#include <functional>
#include <stdexcept>
#include <sys/resource.h>
#ifndef FP_PORTABLE_SHA256
#include <openssl/sha.h>
#else
// Portable SHA-256 (FIPS 180-4) with OpenSSL's interface, for machines without OpenSSL headers
// (compile with -DFP_PORTABLE_SHA256).  Several times slower than OpenSSL's accelerated code.
struct SHA256_CTX { uint32_t h[8]; uint64_t len; unsigned char buf[64]; size_t fill; };
static const uint32_t SHA_K[64] = {0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
static inline uint32_t sha_rotr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }
static void sha_block(SHA256_CTX* c, const unsigned char* p) {
    uint32_t w[64], s[8];
    for (int i = 0; i < 16; i++) w[i] = ((uint32_t)p[4 * i] << 24) | ((uint32_t)p[4 * i + 1] << 16) | ((uint32_t)p[4 * i + 2] << 8) | p[4 * i + 3];
    for (int i = 16; i < 64; i++) {
        uint32_t a = sha_rotr(w[i - 15], 7) ^ sha_rotr(w[i - 15], 18) ^ (w[i - 15] >> 3), b = sha_rotr(w[i - 2], 17) ^ sha_rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16] + a + w[i - 7] + b;
    }
    for (int i = 0; i < 8; i++) s[i] = c->h[i];
    for (int i = 0; i < 64; i++) {
        uint32_t S1 = sha_rotr(s[4], 6) ^ sha_rotr(s[4], 11) ^ sha_rotr(s[4], 25), ch = (s[4] & s[5]) ^ (~s[4] & s[6]);
        uint32_t t1 = s[7] + S1 + ch + SHA_K[i] + w[i];
        uint32_t S0 = sha_rotr(s[0], 2) ^ sha_rotr(s[0], 13) ^ sha_rotr(s[0], 22), mj = (s[0] & s[1]) ^ (s[0] & s[2]) ^ (s[1] & s[2]);
        uint32_t t2 = S0 + mj;
        s[7] = s[6]; s[6] = s[5]; s[5] = s[4]; s[4] = s[3] + t1; s[3] = s[2]; s[2] = s[1]; s[1] = s[0]; s[0] = t1 + t2;
    }
    for (int i = 0; i < 8; i++) c->h[i] += s[i];
}
static int SHA256_Init(SHA256_CTX* c) { static const uint32_t h0[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19}; memcpy(c->h, h0, sizeof h0); c->len = 0; c->fill = 0; return 1; }
static int SHA256_Update(SHA256_CTX* c, const void* data, size_t n) {
    const unsigned char* p = (const unsigned char*)data; c->len += n;
    if (c->fill) { size_t t = 64 - c->fill < n ? 64 - c->fill : n; memcpy(c->buf + c->fill, p, t); c->fill += t; p += t; n -= t; if (c->fill == 64) { sha_block(c, c->buf); c->fill = 0; } }
    for (; n >= 64; p += 64, n -= 64) sha_block(c, p);
    if (n) { memcpy(c->buf, p, n); c->fill = n; }
    return 1;
}
static int SHA256_Final(unsigned char* out, SHA256_CTX* c) {
    uint64_t bits = c->len * 8; unsigned char pad[72] = {0x80}; size_t padlen = (c->fill < 56 ? 56 : 120) - c->fill;
    unsigned char lenb[8]; for (int i = 0; i < 8; i++) lenb[i] = (unsigned char)(bits >> (56 - 8 * i));
    SHA256_Update(c, pad, padlen); SHA256_Update(c, lenb, 8);
    for (int i = 0; i < 8; i++) { out[4 * i] = (unsigned char)(c->h[i] >> 24); out[4 * i + 1] = (unsigned char)(c->h[i] >> 16); out[4 * i + 2] = (unsigned char)(c->h[i] >> 8); out[4 * i + 3] = (unsigned char)c->h[i]; }
    return 1;
}
static unsigned char* SHA256(const unsigned char* p, size_t n, unsigned char* out) { SHA256_CTX c; SHA256_Init(&c); SHA256_Update(&c, p, n); SHA256_Final(out, &c); return out; }
#endif
#ifdef __APPLE__
#define RSS_TO_MB(x) ((x) / (1024.0 * 1024.0))                  // ru_maxrss is in bytes on macOS
#else
#define RSS_TO_MB(x) ((x) / 1024.0)                             // and in kilobytes on Linux
#endif
using namespace std;
typedef unsigned __int128 u128; typedef uint64_t u64; typedef uint8_t u8; typedef uint32_t u32;

// ------------------------------------------------------------------ Z_q,  q = 2^78 + 100663297
static const u64 CQ = 100663297ULL;
static const u128 Q = (((u128)1) << 78) + CQ;
static const u128 M78 = (((u128)1) << 78) - 1;
static const u128 M79 = (((u128)1) << 79) - 1;
static const int TWO_ADICITY = 24, EB = 10, SALT = 16;
static const u64 P_PLAIN = 2;

struct U192 { u64 l0, l1, l2; };
static inline U192 mulwide(u128 a, u128 b) {
    u64 a0 = (u64)a, a1 = (u64)(a >> 64), b0 = (u64)b, b1 = (u64)(b >> 64);
    u128 p00 = (u128)a0 * b0, mid = (u128)a0 * b1 + (u128)a1 * b0;
    u128 t = (p00 >> 64) + (u64)mid;
    U192 r; r.l0 = (u64)p00; r.l1 = (u64)t; r.l2 = (u64)(t >> 64) + (u64)(mid >> 64) + a1 * b1;
    return r;
}
static inline void add192(U192& x, const U192& y) {
    u128 s = (u128)x.l0 + y.l0; x.l0 = (u64)s;
    s = (u128)x.l1 + y.l1 + (u64)(s >> 64); x.l1 = (u64)s;
    x.l2 = x.l2 + y.l2 + (u64)(s >> 64);
}
static inline u128 csub(u128 r) {                               // r < 2q  ->  r mod q, without a branch
    u128 t = r - Q; return t + (Q & ((u128)0 - (t >> 127)));
}
static inline u128 red192(const U192& x) {                    // x < 2^160  ->  x mod q, using 2^78 = -CQ (mod q)
    u128 lo = (((u128)(x.l1 & 0x3FFF)) << 64) | x.l0;
    u128 hi = ((u128)x.l2 << 50) | (x.l1 >> 14);
    u128 t = (u128)CQ * (u64)hi + (((u128)CQ * (u64)(hi >> 64)) << 64);
    u128 r = lo + (u128)CQ * (u64)(t >> 78) + (Q - (t & M78));     // < 3q
    return csub(csub(r));
}
static inline u128 mulq(u128 a, u128 b) { return red192(mulwide(a, b)); }
static inline u128 addq(u128 a, u128 b) { return csub(a + b); }
static inline u128 subq(u128 a, u128 b) { u128 t = a - b; return t + (Q & ((u128)0 - (t >> 127))); }
static inline u128 negq(u128 a) { return a ? Q - a : 0; }
static u128 powq(u128 b, u128 e) { u128 r = 1; while (e) { if (e & 1) r = mulq(r, b); b = mulq(b, b); e >>= 1; } return r; }
static u128 invq(u128 a) { return powq(a, Q - 2); }
static u128 ROOT;                                              // primitive 2^24-th root of unity
static int g_rate_inv = 4;                                     // inverse code rate, as fp_core.RATE_INV (env FP_RATE_INV)
static int g_prox_div = 3;                                     // proximity regime, as fp_core.PROX_DIV (env FP_PROX_DIV)
static bool g_store = false;                                   // keep the encoded matrix in memory (one encoding pass)

// ------------------------------------------------------------------ F = Z_q[t]/(t^2 - 3)
struct F { u128 a, b; };
static inline bool operator==(const F& x, const F& y) { return x.a == y.a && x.b == y.b; }
static inline bool operator!=(const F& x, const F& y) { return !(x == y); }
static const F FZERO{0, 0}, FONE{1, 0}, FT{0, 1};
static inline F fint(u64 c) { return F{(u128)c, 0}; }
static inline F fadd(const F& x, const F& y) { return F{addq(x.a, y.a), addq(x.b, y.b)}; }
static inline F fsub(const F& x, const F& y) { return F{subq(x.a, y.a), subq(x.b, y.b)}; }
static inline F fneg(const F& x) { return F{negq(x.a), negq(x.b)}; }
static inline F fmul(const F& x, const F& y) {
    U192 p0 = mulwide(x.a, y.a), p1 = mulwide(x.b, y.b), s = p1;
    add192(s, p1); add192(s, p1); add192(s, p0);                // a c + 3 b d
    U192 q0 = mulwide(x.a, y.b), q1 = mulwide(x.b, y.a); add192(q0, q1);
    return F{red192(s), red192(q0)};
}
static inline F fscale(const F& x, u128 c) { return F{mulq(x.a, c), mulq(x.b, c)}; }
static F finv(const F& x) {
    u128 d = invq(subq(mulq(x.a, x.a), mulq(3, mulq(x.b, x.b))));
    return F{mulq(x.a, d), mulq(negq(x.b), d)};
}
static F fdot(const F* x, const F* y, size_t n) { F s = FZERO; for (size_t i = 0; i < n; i++) s = fadd(s, fmul(x[i], y[i])); return s; }
static F fdot_base(const F* f, const u128* b, size_t n) {
    F s = FZERO;
    for (size_t i = 0; i < n; i++) if (b[i]) s = fadd(s, fscale(f[i], b[i]));
    return s;
}
static inline void acc_small(F& acc, const F& coef, u128 v) {    // acc += coef * v, cheap for v in {0, 1, -1}
    if (v == 0) return;
    if (v == 1) acc = fadd(acc, coef);
    else if (v == Q - 1) acc = fsub(acc, coef);
    else acc = fadd(acc, fscale(coef, v));
}

struct Reject : runtime_error { using runtime_error::runtime_error; };
static inline int log2i(long n) { if (n <= 0 || (n & (n - 1))) throw runtime_error("not a power of two"); return __builtin_ctzl(n); }

// ------------------------------------------------------------------ bytes, hashing
typedef array<u8, 32> Hash;
static Hash sha(const u8* p, size_t n) { Hash h; SHA256(p, n, h.data()); return h; }
static Hash sha(const vector<u8>& v) { return sha(v.data(), v.size()); }
static inline void wr_base(u8* p, u128 x) { for (int i = 0; i < EB; i++) p[i] = (u8)(x >> (8 * (EB - 1 - i))); }
static inline u128 rd_base(const u8* p) { u128 v = 0; for (int i = 0; i < EB; i++) v = (v << 8) | p[i]; return v; }
static void put_base(vector<u8>& o, u128 x) { size_t n = o.size(); o.resize(n + EB); wr_base(&o[n], x); }
static void put_f(vector<u8>& o, const F& x) { put_base(o, x.a); put_base(o, x.b); }
static void put_fs(vector<u8>& o, const vector<F>& v) { for (auto& x : v) put_f(o, x); }
static void put_str(vector<u8>& o, const string& s) { o.insert(o.end(), s.begin(), s.end()); }
static void put_hash(vector<u8>& o, const Hash& h) { o.insert(o.end(), h.begin(), h.end()); }

// ------------------------------------------------------------------ Fiat-Shamir challenger (identical to fp_core.FSChallenger)
struct Challenger {
    Hash state; vector<u8> buf; size_t pos = 0; u64 ctr = 0; bool replay = false;
    map<string, vector<F>> logF; map<string, vector<u32>> logI;
    explicit Challenger(const string& domain) { string s = "FP-BGV-v2|" + domain; state = sha((const u8*)s.data(), s.size()); }
    void absorb(const string& label, const vector<u8>& data) {
        if (replay) return;
        vector<u8> t(state.begin(), state.end()); put_str(t, "|A|"); put_str(t, label); put_str(t, "|"); put_hash(t, sha(data));
        state = sha(t); buf.clear(); pos = 0; ctr = 0;
    }
    void ratchet(const string& name) {
        vector<u8> t(state.begin(), state.end()); put_str(t, "|C|"); put_str(t, name);
        state = sha(t); buf.clear(); pos = 0; ctr = 0;
    }
    const u8* take(size_t k) {
        while (buf.size() - pos < k) {
            vector<u8> t(state.begin(), state.end()); put_str(t, "|S|");
            for (int i = 7; i >= 0; i--) t.push_back((u8)(ctr >> (8 * i)));
            Hash h = sha(t); buf.insert(buf.end(), h.begin(), h.end()); ctr++;
        }
        pos += k; return &buf[pos - k];
    }
    u128 base() { for (;;) { u128 v = rd_base(take(EB)) & M79; if (v < Q) return v; } }
    vector<F> getF(const string& name, int n = 1) {
        if (replay) return logF.at(name);
        ratchet(name); vector<F> out(n);
        for (auto& x : out) { x.a = base(); x.b = base(); }
        logF[name] = out; return out;
    }
    vector<u32> getI(const string& name, int n, u32 bound) {
        if (replay) return logI.at(name);
        ratchet(name); vector<u32> out; set<u32> seen;
        while ((int)out.size() < n) {
            const u8* p = take(4); u32 v = (((u32)p[0] << 24) | ((u32)p[1] << 16) | ((u32)p[2] << 8) | p[3]) & (bound - 1);
            if (seen.insert(v).second) out.push_back(v);
        }
        logI[name] = out; return out;
    }
};

// ------------------------------------------------------------------ multilinear helpers
static vector<F> eq_table(const F* r, int len) {
    vector<F> t(1, FONE); t.reserve((size_t)1 << len);
    for (int k = 0; k < len; k++) {
        size_t n = t.size(); t.resize(2 * n); F om = fsub(FONE, r[k]);
        for (size_t i = 0; i < n; i++) { t[n + i] = fmul(t[i], r[k]); t[i] = fmul(t[i], om); }
    }
    return t;
}
static vector<F> eq_table(const vector<F>& r) { return eq_table(r.data(), (int)r.size()); }
static F eq_eval(const vector<F>& r, const vector<F>& s) {
    F acc = FONE;
    for (size_t i = 0; i < r.size(); i++) acc = fmul(acc, fadd(fmul(r[i], s[i]), fmul(fsub(FONE, r[i]), fsub(FONE, s[i]))));
    return acc;
}
static void fold(vector<F>& t, const F& r) {
    size_t h = t.size() / 2;
    for (size_t i = 0; i < h; i++) t[i] = fadd(t[2 * i], fmul(r, fsub(t[2 * i + 1], t[2 * i])));
    t.resize(h);
}
static F mle(vector<F> t, const vector<F>& r) {
    if (t.size() != ((size_t)1 << r.size())) throw runtime_error("mle size");
    for (auto& x : r) fold(t, x);
    return t[0];
}
static F zval(const vector<F>& r) { F acc = FONE; for (auto& x : r) acc = fmul(acc, fmul(x, fsub(FONE, x))); return acc; }
static F interp(const vector<F>& vals, const F& r) {
    int d = (int)vals.size() - 1; static vector<vector<u128>> LAG(64);
    if (LAG[d].empty()) {
        for (int i = 0; i <= d; i++) {
            u128 p = 1;
            for (int j = 0; j <= d; j++) if (j != i) p = mulq(p, i > j ? (u128)(i - j) : Q - (u128)(j - i));
            LAG[d].push_back(invq(p));
        }
    }
    vector<F> diff(d + 1);
    for (int j = 0; j <= d; j++) diff[j] = fsub(r, fint(j));
    F acc = FZERO;
    for (int i = 0; i <= d; i++) {
        F num = FONE;
        for (int j = 0; j <= d; j++) if (j != i) num = fmul(num, diff[j]);
        acc = fadd(acc, fmul(vals[i], fscale(num, LAG[d][i])));
    }
    return acc;
}

// ------------------------------------------------------------------ randomness (benchmark quality)
struct Rng {
    u64 s[4];
    explicit Rng(u64 seed) { for (auto& x : s) { seed += 0x9E3779B97F4A7C15ULL; u64 z = seed; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; x = z ^ (z >> 31); } }
    static inline u64 rotl(u64 x, int k) { return (x << k) | (x >> (64 - k)); }
    u64 next() { u64 r = rotl(s[1] * 5, 7) * 9, t = s[1] << 17; s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl(s[3], 45); return r; }
    u128 base() { for (;;) { u128 v = ((((u128)next()) << 64) | next()) & M79; if (v < Q) return v; } }
    F f() { F x; x.a = base(); x.b = base(); return x; }
    int8_t tern() { for (;;) { u64 v = next() & 3; if (v < 3) return (int8_t)v - 1; } }
    u64 below(u64 n) { return next() % n; }
};
static inline u128 from_i8(int8_t v) { return v == 0 ? 0 : (v == 1 ? 1 : Q - 1); }

// ------------------------------------------------------------------ NTT / Reed-Solomon / Merkle
struct NTT {
    int n = 0, logn = 0; vector<u128> tw; vector<u32> rev;
    NTT() {}
    NTT(int n_, u128 w) : n(n_) {
        logn = log2i(n); tw.assign(n, 1); rev.assign(n, 0);
        for (int i = 1; i < n; i++) rev[i] = (rev[i >> 1] >> 1) | ((u32)(i & 1) << (logn - 1));
        for (int half = 1; half < n; half <<= 1) {
            u128 wl = powq(w, n / (2 * half)), x = 1;
            for (int k = 0; k < half; k++) { tw[half + k] = x; x = mulq(x, wl); }
        }
    }
    void run(u128* a) const {
        for (int i = 0; i < n; i++) if ((int)rev[i] > i) swap(a[i], a[rev[i]]);
        for (int half = 1; half < n; half <<= 1) {
            const u128* t = &tw[half];
            for (int i = 0; i < n; i += 2 * half)
                for (int k = 0; k < half; k++) {
                    u128 u = a[i + k], v = mulq(a[i + k + half], t[k]);
                    a[i + k] = addq(u, v); a[i + k + half] = subq(u, v);
                }
        }
    }
};
struct Merkle {
    vector<vector<Hash>> layers;
    void build(vector<Hash> leaves) {
        layers.clear(); layers.push_back(std::move(leaves));
        while (layers.back().size() > 1) {
            auto& p = layers.back(); vector<Hash> nx(p.size() / 2); u8 b[64];
            for (size_t i = 0; i < nx.size(); i++) { memcpy(b, p[2 * i].data(), 32); memcpy(b + 32, p[2 * i + 1].data(), 32); nx[i] = sha(b, 64); }
            layers.push_back(std::move(nx));
        }
    }
    Hash root() const { return layers.back()[0]; }
    vector<Hash> path(size_t j) const { vector<Hash> o; for (size_t l = 0; l + 1 < layers.size(); l++) { o.push_back(layers[l][j ^ 1]); j >>= 1; } return o; }
};
static Hash merkle_root_from(Hash h, size_t j, const vector<Hash>& path) {
    u8 b[64];
    for (auto& s : path) {
        if ((j & 1) == 0) { memcpy(b, h.data(), 32); memcpy(b + 32, s.data(), 32); } else { memcpy(b, s.data(), 32); memcpy(b + 32, h.data(), 32); }
        h = sha(b, 64); j >>= 1;
    }
    return h;
}
static Hash leaf_hash(const u8* salt, const vector<u128>& e) {
    vector<u8> b(SALT + EB * e.size()); memcpy(b.data(), salt, SALT);
    for (size_t i = 0; i < e.size(); i++) wr_base(&b[SALT + EB * i], e[i]);
    return sha(b);
}

// ------------------------------------------------------------------ parameters and layout (as mix_proof.MixParams)
static void code_params(int C, int rate_inv, int qbits, int& k, int& n, int& nq) {
    long nn = (long)rate_inv * C, q = 1;
    for (;;) {
        long kk = C + q;
        while ((long)(rate_inv / 2) * kk > nn || nn - kk < g_prox_div) nn *= 2;
        long e = (nn - kk) / g_prox_div;
        long need = (long)ceil((double)qbits / -log2(1.0 - (double)e / (double)nn));
        if (need <= q) { k = (int)kk; n = (int)nn; nq = (int)q; return; }
        q = need;
    }
}
struct MatP { int C, k, n, nq, R, logn; vector<int> batch_rows; int pm0, pm1; u128 w; };
static MatP make_matp(int C, int rate_inv, int qbits, vector<int> br, int pm0, int pm1) {
    MatP m; m.C = C; code_params(C, rate_inv, qbits, m.k, m.n, m.nq);
    if (m.n > (1 << TWO_ADICITY)) throw runtime_error("code length exceeds the two-adicity of q");
    m.logn = log2i(m.n); m.batch_rows = br; m.R = 0; for (int x : br) m.R += x;
    m.pm0 = pm0; m.pm1 = pm1; m.w = powq(ROOT, (1 << TWO_ADICITY) / m.n);
    return m;
}
static vector<int> sc_degs(int m, int deg, int dl) { vector<int> v(m - 1, deg); v.push_back(dl); return v; }
static int nrows_for(long tab, int C) { return tab <= C ? 1 : (int)(tab / C); }
static int sumv(const vector<int>& v) { int s = 0; for (int x : v) s += x; return s; }
struct Params {
    int N, tau, logN, ell, m, C1, C2, rate_inv, qbits;
    vector<u8> tag() const {                                     // bound into the transcript, as MixParams.tag
        char b[256]; int l = snprintf(b, sizeof b, "mix|N=%d|tau=%d|C1=%d|C2=%d|rate=%d|qbits=%d|prox=%d", N, tau, C1, C2, rate_inv, qbits, g_prox_div);
        return vector<u8>(b, b + l);
    }
    vector<int> dA, dB, dC; int offA, offB, offC, n_mask, rw, rs, c1;
    MatP big, sm; int maskS[4][2]; int row_u[4]; int maskrow;
    Params(int N_, int tau_, int C1_, int C2_, int qbits_, int rate_inv_ = g_rate_inv) : N(N_), tau(tau_), C1(C1_), C2(C2_), rate_inv(rate_inv_), qbits(qbits_) {
        logN = log2i(N); ell = log2i(tau); m = logN + ell;
        dA = sc_degs(ell, 3, 5); dB = sc_degs(logN, 2, 2); dC = sc_degs(m, 4, 7);
        offA = 7; offB = offA + 1 + sumv(dA); offC = offB + 1 + sumv(dB); n_mask = offC + 1 + sumv(dC);
        if (2 * n_mask > C2) throw runtime_error("C2 too small for the mask table");
        rw = nrows_for((long)tau * N, C1); rs = nrows_for(tau, C2);
        big = make_matp(C1, rate_inv, qbits, {3 * rw + 6}, 3 * rw + 4, 3 * rw + 5);
        maskS[0][0] = 3 * rw; maskS[0][1] = 3 * rw + 1; maskS[1][0] = 3 * rw + 2; maskS[1][1] = 3 * rw + 3;
        c1 = rs + 6;
        sm = make_matp(C2, rate_inv, qbits, {c1, 4 * rs + 1}, rs + 4, rs + 5);
        maskS[2][0] = rs; maskS[2][1] = rs + 1; maskS[3][0] = rs + 2; maskS[3][1] = rs + 3;
        for (int i = 0; i < 4; i++) row_u[i] = c1 + i * rs;
        maskrow = c1 + 4 * rs;
    }
};

// ------------------------------------------------------------------ zero-knowledge sumcheck (as fp_core)
struct SCMask {
    vector<int> degs; F a0; vector<vector<F>> c;
    SCMask() {}
    SCMask(const vector<int>& d, Rng& rng) : degs(d) { a0 = rng.f(); for (int x : d) { vector<F> row(x); for (auto& y : row) y = rng.f(); c.push_back(row); } }
    vector<F> entries() const { vector<F> o{a0}; for (auto& r : c) for (auto& x : r) o.push_back(x); return o; }
    F total() const {
        int m = (int)degs.size(); F s = FZERO; for (auto& r : c) for (auto& x : r) s = fadd(s, x);
        return fadd(fscale(a0, powq(2, m)), fscale(s, powq(2, m - 1)));
    }
    F uni(int j, const F& x) const { F acc = FZERO, p = FONE; for (auto& cf : c[j]) { p = fmul(p, x); acc = fadd(acc, fmul(cf, p)); } return acc; }
    vector<F> round_evals(int j, const vector<F>& pref) const {
        int m = (int)degs.size(), rem = m - j - 1; F base = a0, tail = FZERO;
        for (int i = 0; i < j; i++) base = fadd(base, uni(i, pref[i]));
        for (int i = j + 1; i < m; i++) for (auto& x : c[i]) tail = fadd(tail, x);
        vector<F> out;
        for (int cp = 0; cp <= degs[j]; cp++) {
            F v = fscale(fadd(base, uni(j, fint(cp))), powq(2, rem));
            if (rem >= 1) v = fadd(v, fscale(tail, powq(2, rem - 1)));
            out.push_back(v);
        }
        return out;
    }
    static vector<F> functional(const vector<int>& degs, const vector<F>& r) {
        vector<F> o{FONE};
        for (size_t j = 0; j < degs.size(); j++) { F p = FONE; for (int t = 0; t < degs[j]; t++) { p = fmul(p, r[j]); o.push_back(p); } }
        return o;
    }
};
struct Term { F coef; vector<int> fac; vector<u64> sh; };   // sh (optional): factor q is T(x) - sh[q]
struct SCOut { vector<vector<F>> msgs; vector<F> point, finals; F claim; };

// One round of masking, absorbing and challenge; shared by the generic and the specialised provers.
static F sc_finish_round(Challenger& ch, const string& name, int j, vector<F>& vals, const SCMask& g, const F& rho_g, SCOut& o) {
    vector<F> gv = g.round_evals(j, o.point);
    for (size_t c = 0; c < vals.size(); c++) vals[c] = fadd(vals[c], fmul(rho_g, gv[c]));
    vector<F> send{vals[0]}; send.insert(send.end(), vals.begin() + 2, vals.end());
    vector<u8> b; put_fs(b, send); ch.absorb(name + ".m" + to_string(j), b);
    F r = ch.getF(name + ".r" + to_string(j))[0];
    vector<F> full{vals[0], fsub(o.claim, vals[0])}; full.insert(full.end(), vals.begin() + 2, vals.end());
    o.claim = interp(full, r); o.msgs.push_back(send); o.point.push_back(r);
    return r;
}
// Last round: two entries per table; T(X) = t0 + X (t1 - t0) + mask * Z(prefix) * X (1 - X).
static void sc_last_round(Challenger& ch, const string& name, int j, vector<vector<F>>& tables, const vector<const F*>& tmask,
                          const vector<Term>& terms, int d, const SCMask& g, const F& rho_g, SCOut& o) {
    F zprev = zval(o.point);
    auto uni = [&](int idx, const F& x) {
        F v = fadd(tables[idx][0], fmul(x, fsub(tables[idx][1], tables[idx][0])));
        if (tmask[idx]) v = fadd(v, fmul(fmul(*tmask[idx], zprev), fmul(x, fsub(FONE, x))));
        return v;
    };
    vector<F> vals(d + 1, FZERO);
    for (int c = 0; c <= d; c++) {
        vector<F> tv(tables.size()); for (size_t t = 0; t < tables.size(); t++) tv[t] = uni((int)t, fint(c));
        for (auto& tm : terms) {
            F p = tm.coef;
            for (size_t q = 0; q < tm.fac.size(); q++) { F v = tv[tm.fac[q]]; if (!tm.sh.empty() && tm.sh[q]) v = fsub(v, fint(tm.sh[q])); p = fmul(p, v); }
            vals[c] = fadd(vals[c], p);
        }
    }
    F r = sc_finish_round(ch, name, j, vals, g, rho_g, o);
    o.finals.resize(tables.size());
    for (size_t t = 0; t < tables.size(); t++) o.finals[t] = uni((int)t, r);
}
static SCOut sc_prove(Challenger& ch, const string& name, vector<vector<F>> tables, const vector<const F*>& tmask, const vector<Term>& terms,
                      F claim, int m, int deg, int deg_last, const SCMask& g, const F& rho_g) {
    SCOut o; o.claim = fadd(claim, fmul(rho_g, g.total()));
    size_t nt = tables.size();
    for (int j = 0; j < m; j++) {
        if (j == m - 1) { sc_last_round(ch, name, j, tables, tmask, terms, deg_last, g, rho_g, o); break; }
        int d = deg; size_t half = tables[0].size() / 2;
        vector<F> vals(d + 1, FZERO); vector<F> ev(nt * (d + 1));
        for (size_t i = 0; i < half; i++) {
            for (size_t t = 0; t < nt; t++) {
                F a = tables[t][2 * i], df = fsub(tables[t][2 * i + 1], a);
                ev[t * (d + 1)] = a;
                for (int c = 1; c <= d; c++) { a = fadd(a, df); ev[t * (d + 1) + c] = a; }
            }
            for (int c = 0; c <= d; c++)
                for (auto& tm : terms) {
                    F p = tm.coef;
                    for (size_t q = 0; q < tm.fac.size(); q++) { F v = ev[tm.fac[q] * (d + 1) + c]; if (!tm.sh.empty() && tm.sh[q]) v = fsub(v, fint(tm.sh[q])); p = fmul(p, v); }
                    vals[c] = fadd(vals[c], p);
                }
        }
        F r = sc_finish_round(ch, name, j, vals, g, rho_g, o);
        for (auto& t : tables) fold(t, r);
    }
    return o;
}
static pair<vector<F>, F> sc_verify(Challenger& ch, const string& name, const vector<vector<F>>& msgs, F claim, int m, int deg, int deg_last) {
    if ((int)msgs.size() != m) throw Reject("sumcheck: rounds");
    vector<F> point;
    for (int j = 0; j < m; j++) {
        int d = (j == m - 1) ? deg_last : deg;
        if ((int)msgs[j].size() != d) throw Reject("sumcheck: round length");
        vector<u8> b; put_fs(b, msgs[j]); ch.absorb(name + ".m" + to_string(j), b);
        F r = ch.getF(name + ".r" + to_string(j))[0]; point.push_back(r);
        vector<F> full{msgs[j][0], fsub(claim, msgs[j][0])}; full.insert(full.end(), msgs[j].begin() + 1, msgs[j].end());
        claim = interp(full, r);
    }
    return {point, claim};
}

// ------------------------------------------------------------------ instance, proof
struct Instance {
    int N, tau; vector<u128> a, b; vector<u128> cin, cout;       // cin[(2*i + comp)*N + x]
    Hash digest() const {
        SHA256_CTX c; SHA256_Init(&c); vector<u8> buf((size_t)N * EB);
        auto feed = [&](const u128* p) { for (int x = 0; x < N; x++) wr_base(&buf[(size_t)x * EB], p[x]); SHA256_Update(&c, buf.data(), buf.size()); };
        feed(a.data()); feed(b.data());
        for (int i = 0; i < 2 * tau; i++) feed(&cin[(size_t)i * N]);
        for (int i = 0; i < 2 * tau; i++) feed(&cout[(size_t)i * N]);
        Hash h; SHA256_Final(h.data(), &c); return h;
    }
};
struct ColB { vector<u128> e; array<u8, SALT> salt; vector<Hash> path; };
struct Proof {
    Hash root_big, root_s1, root_s2; vector<F> G; vector<vector<F>> A, B, C; vector<F> evalsA, evalsC; F mu;
    vector<F> vec[4], prox[2]; vector<vector<ColB>> cols[2];     // cols[mat][query][batch]
};
static vector<u8> serialize(const Params& par, const Proof& p) {
    vector<u8> o; put_hash(o, p.root_big); put_hash(o, p.root_s1); put_hash(o, p.root_s2); put_fs(o, p.G);
    for (auto& r : p.A) put_fs(o, r); put_fs(o, p.evalsA);
    for (auto& r : p.B) put_fs(o, r); for (auto& r : p.C) put_fs(o, r); put_fs(o, p.evalsC); put_f(o, p.mu);
    for (int s = 0; s < 4; s++) put_fs(o, p.vec[s]); for (int mi = 0; mi < 2; mi++) put_fs(o, p.prox[mi]);
    for (int mi = 0; mi < 2; mi++) for (auto& q : p.cols[mi]) for (auto& cb : q) {
        for (u128 x : cb.e) put_base(o, x);
        o.insert(o.end(), cb.salt.begin(), cb.salt.end()); for (auto& h : cb.path) put_hash(o, h);
    }
    (void)par; return o;
}
static Proof deserialize(const Params& par, const vector<u8>& d) {
    size_t pos = 0;
    auto take = [&](size_t n) { if (pos + n > d.size()) throw Reject("proof too short"); pos += n; return &d[pos - n]; };
    auto base = [&]() { u128 v = rd_base(take(EB)); if (v >= Q) throw Reject("non-canonical element"); return v; };
    auto f = [&]() { F x; x.a = base(); x.b = base(); return x; };
    auto fs = [&](int n) { vector<F> v(n); for (auto& x : v) x = f(); return v; };
    auto hs = [&]() { Hash h; memcpy(h.data(), take(32), 32); return h; };
    Proof p; p.root_big = hs(); p.root_s1 = hs(); p.root_s2 = hs(); p.G = fs(3);
    for (int dd : par.dA) p.A.push_back(fs(dd)); p.evalsA = fs(4);
    for (int dd : par.dB) p.B.push_back(fs(dd)); for (int dd : par.dC) p.C.push_back(fs(dd)); p.evalsC = fs(3); p.mu = f();
    p.vec[0] = fs(par.big.k); p.vec[1] = fs(par.big.k); p.vec[2] = fs(par.sm.k); p.vec[3] = fs(par.sm.k);
    p.prox[0] = fs(par.big.k); p.prox[1] = fs(par.sm.k);
    const MatP* mp[2] = {&par.big, &par.sm};
    for (int mi = 0; mi < 2; mi++) {
        p.cols[mi].resize(mp[mi]->nq);
        for (auto& q : p.cols[mi]) for (int cnt : mp[mi]->batch_rows) {
            ColB cb; cb.e.resize(cnt); for (auto& x : cb.e) x = base();
            memcpy(cb.salt.data(), take(SALT), SALT); for (int l = 0; l < mp[mi]->logn; l++) cb.path.push_back(hs());
            q.push_back(std::move(cb));
        }
    }
    if (pos != d.size()) throw Reject("trailing bytes");
    return p;
}

// ------------------------------------------------------------------ verifier-side derivation of the nine linear claims
// negacyclic NTT for Z_q[X]/(X^N+1)
struct Ring {
    int N; NTT fw, bw; vector<u128> psi, ipsi;
    explicit Ring(int N_) : N(N_) {
        u128 ps = powq(ROOT, (1 << TWO_ADICITY) / (2 * N)), om = mulq(ps, ps);
        fw = NTT(N, om); bw = NTT(N, invq(om)); psi.resize(N); ipsi.resize(N);
        u128 x = 1, ix = invq(N), ip = invq(ps);
        for (int i = 0; i < N; i++) { psi[i] = x; ipsi[i] = ix; x = mulq(x, ps); ix = mulq(ix, ip); }
    }
    void to(vector<u128>& a) const { for (int i = 0; i < N; i++) a[i] = mulq(a[i], psi[i]); fw.run(a.data()); }
    void from(vector<u128>& a) const { bw.run(a.data()); for (int i = 0; i < N; i++) a[i] = mulq(a[i], ipsi[i]); }
};
struct Pub { vector<F> zpub, zhat, rp[3]; };
static Pub public_projection(const Params& par, const Instance& in, const vector<F>& ru, const vector<F>& rv) {
    int N = par.N, tau = par.tau; Pub P; P.zpub.resize(tau); P.zhat.resize(tau);
    for (int i = 0; i < tau; i++) {
        P.zpub[i] = fadd(fdot_base(ru.data(), &in.cin[(size_t)(2 * i) * N], N), fdot_base(rv.data(), &in.cin[(size_t)(2 * i + 1) * N], N));
        P.zhat[i] = fadd(fdot_base(ru.data(), &in.cout[(size_t)(2 * i) * N], N), fdot_base(rv.data(), &in.cout[(size_t)(2 * i + 1) * N], N));
    }
    // rho'_r[y] = sum_x rho_u[x] coeff_x(a X^y) + rho_v[x] coeff_x(b X^y) = coeff_y(a* rho_u + b* rho_v),
    // where a*(X) = a(1/X) is the adjoint of multiplication by a in Z_q[X]/(X^N+1):  a*_0 = a_0, a*_j = -a_{N-j}.
    Ring R(N);
    auto star = [&](const vector<u128>& p) { vector<u128> t(N); t[0] = p[0]; for (int j = 1; j < N; j++) t[j] = negq(p[N - j]); R.to(t); return t; };
    vector<u128> as = star(in.a), bs = star(in.b), x0(N), x1(N), y0(N), y1(N);
    for (int i = 0; i < N; i++) { x0[i] = ru[i].a; x1[i] = ru[i].b; y0[i] = rv[i].a; y1[i] = rv[i].b; }
    R.to(x0); R.to(x1); R.to(y0); R.to(y1);
    for (int i = 0; i < N; i++) { x0[i] = addq(mulq(as[i], x0[i]), mulq(bs[i], y0[i])); x1[i] = addq(mulq(as[i], x1[i]), mulq(bs[i], y1[i])); }
    R.from(x0); R.from(x1);
    P.rp[0].resize(N); P.rp[1].resize(N); P.rp[2].resize(N);
    for (int y = 0; y < N; y++) { P.rp[0][y] = F{x0[y], x1[y]}; P.rp[1][y] = fscale(ru[y], P_PLAIN); P.rp[2][y] = fscale(rv[y], P_PLAIN); }
    return P;
}
struct Derived { vector<F> r, ry, rz; F val[9]; F rhoB; F rp_ry[3]; };
static void chk_shape(const Params& par, const Proof& p) {
    auto bad = [](const char* w) { throw Reject(string("malformed proof: ") + w); };
    if (p.G.size() != 3 || p.evalsA.size() != 4 || p.evalsC.size() != 3) bad("values");
    auto chk = [&](const vector<vector<F>>& m, const vector<int>& d) { if (m.size() != d.size()) bad("sumcheck"); for (size_t i = 0; i < d.size(); i++) if ((int)m[i].size() != d[i]) bad("sumcheck round"); };
    chk(p.A, par.dA); chk(p.B, par.dB); chk(p.C, par.dC);
}
static Derived derive(const Params& par, const Instance& in, const Hash& stmt, const Proof& pf, Challenger& ch, const Pub* cached, Pub* keep) {
    chk_shape(par, pf);
    int N = par.N, ell = par.ell, logN = par.logN, m = par.m; Derived D;
    ch.absorb("params", par.tag()); ch.absorb("stmt", vector<u8>(stmt.begin(), stmt.end()));
    { vector<u8> b; put_hash(b, pf.root_big); put_hash(b, pf.root_s1); ch.absorb("round1", b); }
    vector<F> ru = ch.getF("rho_u", N), rv = ch.getF("rho_v", N), ab = ch.getF("ab", 2);
    F alpha = ab[0], beta = ab[1];
    Pub local; const Pub* P = cached;
    if (!P) { local = public_projection(par, in, ru, rv); P = &local; }
    { vector<u8> b; put_hash(b, pf.root_s2); put_fs(b, pf.G); ch.absorb("round2", b); }
    vector<F> tc = ch.getF("tc", ell), kA = ch.getF("kA", 3); F rhoA = ch.getF("rhoA")[0];
    auto [r, clA] = sc_verify(ch, "A", pf.A, fadd(fadd(kA[0], kA[1]), fmul(rhoA, pf.G[0])), ell, 3, 5);
    F U = pf.evalsA[0], Uh = pf.evalsA[1], s_val = pf.evalsA[2], Hd = pf.evalsA[3];
    { vector<u8> b; put_fs(b, pf.evalsA); ch.absorb("evalsA", b); }
    F Hh = fsub(fadd(mle(P->zhat, r), fmul(beta, s_val)), alpha);
    F fA = fadd(fmul(eq_eval(tc, r), fadd(fmul(kA[0], fmul(U, Hd)), fmul(kA[1], fmul(Uh, Hh)))), fmul(kA[2], fsub(U, Uh)));
    if (rhoA == FZERO) throw Reject("degenerate challenge");
    F gvalA = fmul(fsub(clA, fA), finv(rhoA));
    F rhoB = ch.getF("rhoB")[0];
    F idr = FZERO; for (int b = 0; b < ell; b++) idr = fadd(idr, fscale(r[b], (u128)1 << b));
    F Sp = fadd(fsub(fsub(Hd, mle(P->zpub, r)), fmul(beta, idr)), alpha);
    auto [ry, clB] = sc_verify(ch, "B", pf.B, fadd(Sp, fmul(rhoB, pf.G[1])), logN, 2, 2);
    vector<F> tz = ch.getF("tz", m), kC = ch.getF("kC", 3); F rhoC = ch.getF("rhoC")[0];
    auto [rz, clC] = sc_verify(ch, "C", pf.C, fmul(rhoC, pf.G[2]), m, 4, 7);
    { vector<u8> b; put_fs(b, pf.evalsC); ch.absorb("evalsC", b); }
    F s3 = FZERO;
    for (int k = 0; k < 3; k++) { F w = pf.evalsC[k]; s3 = fadd(s3, fmul(kC[k], fsub(fmul(fmul(w, w), w), w))); }
    if (rhoC == FZERO) throw Reject("degenerate challenge");
    F gvalC = fmul(fsub(clC, fmul(eq_eval(tz, rz), s3)), finv(rhoC));
    D.r = r; D.ry = ry; D.rz = rz; D.rhoB = rhoB;
    for (int k = 0; k < 3; k++) D.rp_ry[k] = mle(P->rp[k], ry);
    D.val[0] = U; D.val[1] = Uh; D.val[2] = s_val; D.val[3] = clB;
    for (int k = 0; k < 3; k++) D.val[4 + k] = pf.evalsC[k];
    D.val[7] = gvalA; D.val[8] = gvalC;
    if (keep && !cached) *keep = std::move(local);
    return D;
}
static vector<F> lo_vec(const vector<F>& pt, int C, long tab) {
    if (tab >= C) return eq_table(pt.data(), log2i(C));
    vector<F> v = eq_table(pt); v.resize(C, FZERO); return v;
}
static vector<F> hi_coefs(const vector<F>& pt, int C, long tab) {
    if (tab > C) { int lc = log2i(C); return eq_table(pt.data() + lc, (int)pt.size() - lc); }
    return vector<F>{FONE};
}
struct Slots { vector<F> rowcoef[4]; vector<char> used[4]; vector<F> L[4]; F V; };
static Slots compile_slots(const Params& par, const Derived& D, const vector<F>& kap) {
    int N = par.N, tau = par.tau, C1 = par.C1, C2 = par.C2, rw = par.rw; long TN = (long)tau * N;
    Slots S; S.V = FZERO;
    for (int i = 0; i < 9; i++) S.V = fadd(S.V, fmul(kap[i], D.val[i]));
    for (int s = 0; s < 4; s++) { int R = s < 2 ? par.big.R : par.sm.R; S.rowcoef[s].assign(R, FZERO); S.used[s].assign(R, 0); }
    vector<F> ptB = D.ry; ptB.insert(ptB.end(), D.r.begin(), D.r.end());
    S.L[0] = lo_vec(ptB, C1, TN); S.L[1] = lo_vec(D.rz, C1, TN); S.L[2] = lo_vec(D.r, C2, tau); S.L[3].assign(C2, FZERO);
    vector<F> hiB = hi_coefs(ptB, C1, TN), hiz = hi_coefs(D.rz, C1, TN), hir = hi_coefs(D.r, C2, tau);
    auto tab = [&](int s, int start, const vector<F>& hi, const F& coef) {
        for (size_t i = 0; i < hi.size(); i++) { S.rowcoef[s][start + i] = fadd(S.rowcoef[s][start + i], fmul(coef, hi[i])); S.used[s][start + i] = 1; }
    };
    F Zr = zval(D.r), Zrz = zval(D.rz);
    auto unit = [&](int e, const F& coef) { S.L[3][2 * e] = fadd(S.L[3][2 * e], coef); S.L[3][2 * e + 1] = fadd(S.L[3][2 * e + 1], fmul(coef, FT)); };
    auto gfun = [&](int off, const vector<F>& cf, const F& coef) { for (size_t i = 0; i < cf.size(); i++) unit(off + (int)i, fmul(coef, cf[i])); };
    S.rowcoef[3][par.maskrow] = FONE; S.used[3][par.maskrow] = 1;
    tab(2, par.row_u[0], hir, kap[0]); tab(2, par.row_u[1], hir, fmul(kap[0], FT)); unit(0, fmul(kap[0], Zr));
    tab(2, par.row_u[2], hir, kap[1]); tab(2, par.row_u[3], hir, fmul(kap[1], FT)); unit(1, fmul(kap[1], Zr));
    tab(2, 0, hir, kap[2]); unit(2, fmul(kap[2], Zr));
    for (int k = 0; k < 3; k++) tab(0, k * rw, hiB, fmul(kap[3], D.rp_ry[k]));
    unit(3, fmul(kap[3], fscale(Zr, invq(N))));
    gfun(par.offB, SCMask::functional(par.dB, D.ry), fmul(kap[3], D.rhoB));
    for (int k = 0; k < 3; k++) { tab(1, k * rw, hiz, kap[4 + k]); unit(4 + k, fmul(kap[4 + k], Zrz)); }
    gfun(par.offA, SCMask::functional(par.dA, D.r), kap[7]);
    gfun(par.offC, SCMask::functional(par.dC, D.rz), kap[8]);
    return S;
}
static void encode_ext(const MatP& mp, const NTT& ntt, const vector<F>& u, vector<u128>& e0, vector<u128>& e1) {
    e0.assign(mp.n, 0); e1.assign(mp.n, 0);
    for (size_t i = 0; i < u.size(); i++) { e0[i] = u[i].a; e1[i] = u[i].b; }
    ntt.run(e0.data()); ntt.run(e1.data());
}
static void verify_proof(const Params& par, const Instance& in, const Proof& pf) {
    Challenger ch("mix"); Hash stmt = in.digest();
    Derived D = derive(par, in, stmt, pf, ch, nullptr, nullptr);
    vector<F> kap = ch.getF("pcs.kappa", 9);
    Slots S = compile_slots(par, D, kap);
    { vector<u8> b; put_f(b, pf.mu); ch.absorb("pcs.mu", b); }
    F c = ch.getF("pcs.c")[0];
    const MatP* mp[2] = {&par.big, &par.sm};
    for (int s = 0; s < 4; s++) if ((int)pf.vec[s].size() != mp[s / 2]->k) throw Reject("opening: vector length");
    vector<F> gam[2];
    for (int mi = 0; mi < 2; mi++) { if ((int)pf.prox[mi].size() != mp[mi]->k) throw Reject("opening: vector length"); gam[mi] = ch.getF(mi == 0 ? "pcs.gamma.big" : "pcs.gamma.small", mp[mi]->R); }
    { vector<u8> b; for (int s = 0; s < 4; s++) put_fs(b, pf.vec[s]); for (int mi = 0; mi < 2; mi++) put_fs(b, pf.prox[mi]); ch.absorb("pcs.vec", b); }
    F lhs = FZERO;
    for (int s = 0; s < 4; s++) lhs = fadd(lhs, fdot(pf.vec[s].data(), S.L[s].data(), mp[s / 2]->C));
    if (lhs != fadd(pf.mu, fmul(c, S.V))) throw Reject("opening: claimed values");
    const Hash* roots[2][2] = {{&pf.root_big, nullptr}, {&pf.root_s1, &pf.root_s2}};
    for (int mi = 0; mi < 2; mi++) {
        const MatP& M = *mp[mi]; NTT ntt(M.n, M.w);
        vector<u32> J = ch.getI(mi == 0 ? "pcs.J.big" : "pcs.J.small", M.nq, M.n);
        vector<u128> p0, p1, v0[2], v1[2];
        encode_ext(M, ntt, pf.prox[mi], p0, p1);
        for (int t = 0; t < 2; t++) encode_ext(M, ntt, pf.vec[2 * mi + t], v0[t], v1[t]);
        if ((int)pf.cols[mi].size() != M.nq) throw Reject("opening: number of columns");
        vector<u128> col(M.R);
        for (int q = 0; q < M.nq; q++) {
            u32 j = J[q]; const auto& pb = pf.cols[mi][q];
            if (pb.size() != M.batch_rows.size()) throw Reject("opening: batches");
            int at = 0;
            for (size_t b = 0; b < pb.size(); b++) {
                if ((int)pb[b].e.size() != M.batch_rows[b] || (int)pb[b].path.size() != M.logn) throw Reject("opening: malformed column");
                for (u128 x : pb[b].e) { if (x >= Q) throw Reject("opening: malformed column"); col[at++] = x; }
                if (merkle_root_from(leaf_hash(pb[b].salt.data(), pb[b].e), j, pb[b].path) != *roots[mi][b]) throw Reject("opening: Merkle path");
            }
            F s{col[M.pm0], col[M.pm1]};
            for (int i = 0; i < M.R; i++) if (i != M.pm0 && i != M.pm1) acc_small(s, gam[mi][i], col[i]);
            if (s != F{p0[j], p1[j]}) throw Reject("opening: proximity vector");
            for (int t = 0; t < 2; t++) {
                int sid = 2 * mi + t; F a = FZERO;
                for (int i = 0; i < M.R; i++) if (S.used[sid][i]) acc_small(a, S.rowcoef[sid][i], col[i]);
                F cmb = fmul(c, a);
                if (F{addq(col[par.maskS[sid][0]], cmb.a), addq(col[par.maskS[sid][1]], cmb.b)} != F{v0[t][j], v1[t][j]}) throw Reject("opening: combination vector");
            }
        }
    }
}

// ------------------------------------------------------------------ prover-side committed matrix (streaming)
struct Mat {
    MatP mp; NTT ntt; Rng* rng;
    function<void(int, u128*)> get_msg;                           // writes the k message symbols of a row
    struct Batch { int start, cnt; vector<array<u8, SALT>> salts; Merkle tree; };
    vector<Batch> batches; vector<vector<u128>> enc;             // enc: only filled when g_store
    Mat(const MatP& m, Rng* r) : mp(m), ntt(m.n, m.w), rng(r) {}
    Hash commit(int start, int cnt) {                             // rows [start, start+cnt) must be available through get_msg
        Batch B; B.start = start; B.cnt = cnt; B.salts.resize(mp.n);
        vector<SHA256_CTX> ctx(mp.n);
        for (int j = 0; j < mp.n; j++) { for (auto& x : B.salts[j]) x = (u8)rng->next(); SHA256_Init(&ctx[j]); SHA256_Update(&ctx[j], B.salts[j].data(), SALT); }
        vector<u128> buf(mp.n); u8 eb[EB];
        for (int r = start; r < start + cnt; r++) {
            fill(buf.begin() + mp.k, buf.end(), 0); get_msg(r, buf.data()); ntt.run(buf.data());
            for (int j = 0; j < mp.n; j++) { wr_base(eb, buf[j]); SHA256_Update(&ctx[j], eb, EB); }
            if (g_store) { if ((int)enc.size() <= r) enc.resize(r + 1); enc[r] = buf; }
        }
        vector<Hash> leaves(mp.n);
        for (int j = 0; j < mp.n; j++) SHA256_Final(leaves[j].data(), &ctx[j]);
        B.tree.build(std::move(leaves)); Hash root = B.tree.root(); batches.push_back(std::move(B)); return root;
    }
    vector<F> frow(int r0, int r1) {
        vector<u128> a(mp.k), b(mp.k); get_msg(r0, a.data()); get_msg(r1, b.data());
        vector<F> o(mp.k); for (int x = 0; x < mp.k; x++) o[x] = F{a[x], b[x]}; return o;
    }
    vector<F> comb(const vector<F>& coef, const vector<char>& used) {
        vector<F> o(mp.k, FZERO); vector<u128> row(mp.k);
        for (int r = 0; r < mp.R; r++) if (used[r]) { get_msg(r, row.data()); for (int x = 0; x < mp.k; x++) acc_small(o[x], coef[r], row[x]); }
        return o;
    }
    vector<vector<ColB>> open(const vector<u32>& J) {            // second pass over the rows
        vector<vector<ColB>> out(J.size());
        for (auto& q : out) { q.resize(batches.size()); for (size_t b = 0; b < batches.size(); b++) q[b].e.resize(batches[b].cnt); }
        vector<u128> buf(mp.n);
        for (size_t b = 0; b < batches.size(); b++)
            for (int r = 0; r < batches[b].cnt; r++) {
                if (g_store) { const auto& e = enc[batches[b].start + r]; for (size_t q = 0; q < J.size(); q++) out[q][b].e[r] = e[J[q]]; continue; }
                fill(buf.begin() + mp.k, buf.end(), 0); get_msg(batches[b].start + r, buf.data()); ntt.run(buf.data());
                for (size_t q = 0; q < J.size(); q++) out[q][b].e[r] = buf[J[q]];
            }
        for (size_t q = 0; q < J.size(); q++) for (size_t b = 0; b < batches.size(); b++) { out[q][b].salt = batches[b].salts[J[q]]; out[q][b].path = batches[b].tree.path(J[q]); }
        return out;
    }
};

// ------------------------------------------------------------------ prover
struct Witness { vector<int8_t> W[3]; vector<u32> sigma; };      // W[k][y + N*i]
struct Timer { chrono::steady_clock::time_point t0 = chrono::steady_clock::now(); double lap() { auto t = chrono::steady_clock::now(); double d = chrono::duration<double>(t - t0).count(); t0 = t; return d; } };
static map<string, double> g_time;

// Sumcheck C (shortness), specialised and streaming.
//   * eq(tz, x) is never materialised: the round polynomial is  E_j * l_j(X) * t_j(X)  with
//     t_j(X) = sum_x eq(tz_{>j}, x) P(r_{<j}, X, x)  of degree 3; t_j(1) follows from the running claim,
//     so P is evaluated at X = 0, 2, 3 only, against two small eq tables (split low / high variables).
//   * the first KS rounds read the ternary witness directly (round 0: small integers; rounds 1-2:
//     lookup tables over all 3^4 / 3^8 patterns; later: sign-controlled sums), so the folded tables
//     are first materialised at 1/2^KS of the witness size.
static SCOut sumcheck_C(Challenger& ch, const Params& par, const Witness& w, const vector<F>& tz, const vector<F>& kC, const F* aw[3],
                        const SCMask& g, const F& rho_g) {
    const int m = par.m, d = 4; size_t n = (size_t)1 << m;
    SCOut o; o.claim = fmul(rho_g, g.total());
    vector<Term> terms; for (int k = 0; k < 3; k++) { terms.push_back({kC[k], {0, 1 + k, 1 + k, 1 + k}}); terms.push_back({fneg(kC[k]), {0, 1 + k}}); }
    vector<const F*> tm{nullptr, aw[0], aw[1], aw[2]};
    if (m == 1) {                                                  // degenerate: only the last round exists
        vector<vector<F>> tabs{eq_table(tz)}; for (int k = 0; k < 3; k++) { vector<F> t(n); for (size_t i = 0; i < n; i++) t[i] = F{from_i8(w.W[k][i]), 0}; tabs.push_back(t); }
        sc_last_round(ch, "C", 0, tabs, tm, terms, 7, g, rho_g, o); return o;
    }
    const int KS = min(m - 1, 8), sp = (m + 1) / 2;
    F fclaim = FZERO, Ej = FONE; vector<F> E{FONE}, T[3];
    auto cube = [](const F& x) { return fsub(fmul(fmul(x, x), x), x); };
    for (int j = 0; j < m - 1; j++) {
        int lo_bits = max(0, sp - (j + 1)), hi_from = max(sp, j + 1), hi_bits = m - hi_from;
        vector<F> eqLo = eq_table(tz.data() + j + 1, lo_bits), eqHi = eq_table(tz.data() + hi_from, hi_bits);
        size_t nlo = (size_t)1 << lo_bits, nhi = (size_t)1 << hi_bits, blk = (size_t)1 << (j + 1), hb = blk / 2;
        // per-round lookup tables
        vector<F> lut0[3];                                         // round 0: kappa_k * (v^3 - v) for v in [-5, 5]
        vector<F> lut[3][3]; int npat = 0;                         // rounds 1, 2: kappa_k * (w(c)^3 - w(c)) per pattern, c in {0, 2, 3}
        if (j == 0) {
            for (int k = 0; k < 3; k++) for (int v = -5; v <= 5; v++) { long sv = (long)v * v * v - v; lut0[k].push_back(fscale(kC[k], sv >= 0 ? (u128)sv : Q - (u128)(-sv))); }
        } else if (j <= 2 && j < KS) {
            npat = 1; for (size_t i = 0; i < blk; i++) npat *= 3;
            vector<F> A(npat), B(npat);
            for (int pat = 0; pat < npat; pat++) {
                int x = pat; F a = FZERO, b = FZERO;
                for (size_t pos = 0; pos < blk; pos++) { int dg = x % 3 - 1; x /= 3; F& tgt = pos < hb ? a : b; const F& e = E[pos % hb]; if (dg == 1) tgt = fadd(tgt, e); else if (dg == -1) tgt = fsub(tgt, e); }
                A[pat] = a; B[pat] = b;
            }
            for (int k = 0; k < 3; k++) for (int ci = 0; ci < 3; ci++) {
                lut[k][ci].resize(npat);
                for (int pat = 0; pat < npat; pat++) {
                    F df = fsub(B[pat], A[pat]), wv = ci == 0 ? A[pat] : (ci == 1 ? fadd(B[pat], df) : fadd(fadd(B[pat], df), df));
                    lut[k][ci][pat] = fmul(kC[k], cube(wv));
                }
            }
        }
        F t0 = FZERO, t2 = FZERO, t3 = FZERO;
        for (size_t xh = 0; xh < nhi; xh++) {
            F a0 = FZERO, a2 = FZERO, a3 = FZERO;
            for (size_t xl = 0; xl < nlo; xl++) {
                size_t ip = xl + nlo * xh; F p0 = FZERO, p2 = FZERO, p3 = FZERO;
                if (j == 0) {
                    bool any = false;
                    for (int k = 0; k < 3; k++) {
                        int a = w.W[k][2 * ip], b = w.W[k][2 * ip + 1], v2 = 2 * b - a, v3 = 3 * b - 2 * a;
                        if (v2 > 1 || v2 < -1) { p2 = fadd(p2, lut0[k][v2 + 5]); any = true; }
                        if (v3 > 1 || v3 < -1) { p3 = fadd(p3, lut0[k][v3 + 5]); any = true; }
                    }
                    if (!any) continue;
                } else if (j < KS && j <= 2) {
                    for (int k = 0; k < 3; k++) {
                        const int8_t* p = w.W[k].data() + ip * blk; int idx = 0;
                        for (size_t pos = blk; pos-- > 0;) idx = idx * 3 + (p[pos] + 1);
                        p0 = fadd(p0, lut[k][0][idx]); p2 = fadd(p2, lut[k][1][idx]); p3 = fadd(p3, lut[k][2][idx]);
                    }
                } else {
                    for (int k = 0; k < 3; k++) {
                        F A, B;
                        if (j < KS) {
                            const int8_t* p = w.W[k].data() + ip * blk; A = FZERO; B = FZERO;
                            for (size_t bq = 0; bq < hb; bq++) {
                                if (p[bq] == 1) A = fadd(A, E[bq]); else if (p[bq] == -1) A = fsub(A, E[bq]);
                                if (p[hb + bq] == 1) B = fadd(B, E[bq]); else if (p[hb + bq] == -1) B = fsub(B, E[bq]);
                            }
                        } else { A = T[k][2 * ip]; B = T[k][2 * ip + 1]; }
                        F df = fsub(B, A), w2 = fadd(B, df), w3 = fadd(w2, df);
                        p0 = fadd(p0, fmul(kC[k], cube(A))); p2 = fadd(p2, fmul(kC[k], cube(w2))); p3 = fadd(p3, fmul(kC[k], cube(w3)));
                    }
                }
                a0 = fadd(a0, fmul(eqLo[xl], p0)); a2 = fadd(a2, fmul(eqLo[xl], p2)); a3 = fadd(a3, fmul(eqLo[xl], p3));
            }
            t0 = fadd(t0, fmul(eqHi[xh], a0)); t2 = fadd(t2, fmul(eqHi[xh], a2)); t3 = fadd(t3, fmul(eqHi[xh], a3));
        }
        // t_j(1) from the running claim:  E_j [ (1 - tz_j) t(0) + tz_j t(1) ] = fclaim
        F l0 = fsub(FONE, tz[j]), l1 = tz[j];
        if (Ej == FZERO || l1 == FZERO) throw runtime_error("degenerate challenge in sumcheck C");
        F t1 = fmul(fsub(fmul(fclaim, finv(Ej)), fmul(l0, t0)), finv(l1));
        F t4 = fsub(fadd(fscale(t3, 4), fscale(t1, 4)), fadd(fscale(t2, 6), t0));          // cubic: 4 t3 - 6 t2 + 4 t1 - t0
        vector<F> tv{t0, t1, t2, t3, t4}, vals(d + 1);
        F dl = fsub(l1, l0), lc = l0;
        for (int c = 0; c <= d; c++) { vals[c] = fmul(Ej, fmul(lc, tv[c])); lc = fadd(lc, dl); }
        F r = sc_finish_round(ch, "C", j, vals, g, rho_g, o);
        F lr = fadd(l0, fmul(r, dl)), tr = interp(vector<F>{t0, t1, t2, t3}, r);
        fclaim = fmul(Ej, fmul(lr, tr)); Ej = fmul(Ej, lr);
        // state for the next round
        if (j + 1 <= KS) {                                         // extend eq(r_{<j+1}, .): the new variable is the next higher bit
            size_t sz = E.size(); E.resize(2 * sz); F om = fsub(FONE, r);
            for (size_t b = 0; b < sz; b++) { E[sz + b] = fmul(E[b], r); E[b] = fmul(E[b], om); }
        }
        if (j + 1 == KS) {                                         // materialise the folded tables
            size_t cnt = n >> KS, bsz = (size_t)1 << KS;
            for (int k = 0; k < 3; k++) {
                T[k].assign(cnt, FZERO); const int8_t* p = w.W[k].data();
                for (size_t i = 0; i < cnt; i++) { F a = FZERO; for (size_t bq = 0; bq < bsz; bq++) { int8_t v = p[i * bsz + bq]; if (v == 1) a = fadd(a, E[bq]); else if (v == -1) a = fsub(a, E[bq]); } T[k][i] = a; }
            }
        } else if (j + 1 > KS) for (int k = 0; k < 3; k++) fold(T[k], r);
    }
    vector<vector<F>> tabs{vector<F>{fmul(Ej, fsub(FONE, tz[m - 1])), fmul(Ej, tz[m - 1])}, T[0], T[1], T[2]};
    sc_last_round(ch, "C", m - 1, tabs, tm, terms, 7, g, rho_g, o);
    return o;
}

static Proof prove(const Params& par, const Instance& in, const Witness& w, Rng& rng, bool generic_C = false) {
    const int N = par.N, tau = par.tau, ell = par.ell, logN = par.logN, m = par.m, C1 = par.C1, C2 = par.C2, rw = par.rw, rs = par.rs;
    const long TN = (long)tau * N; Proof pf; Timer T; Challenger ch("mix");
    // ---- big matrix: W rows are produced on demand from the ternary tables; only pads and mask rows are stored
    Mat big(par.big, &rng);
    vector<vector<u128>> bpad(3 * rw, vector<u128>(par.big.nq)); for (auto& r : bpad) for (auto& x : r) x = rng.base();
    vector<vector<u128>> bmask(6, vector<u128>(par.big.k)); for (auto& r : bmask) for (auto& x : r) x = rng.base();
    big.get_msg = [&](int row, u128* out) {
        if (row >= 3 * rw) { memcpy(out, bmask[row - 3 * rw].data(), sizeof(u128) * par.big.k); return; }
        const int8_t* p = w.W[row / rw].data() + (size_t)(row % rw) * C1; long len = min<long>(C1, TN);
        for (long x = 0; x < len; x++) out[x] = from_i8(p[x]);
        for (long x = len; x < C1; x++) out[x] = 0;
        memcpy(out + C1, bpad[row].data(), sizeof(u128) * par.big.nq);
    };
    pf.root_big = big.commit(0, par.big.R);
    g_time["1 commit W (encode + hash)"] += T.lap();
    // ---- small matrix: stored
    Mat sm(par.sm, &rng); vector<vector<u128>> smsg;              // full messages (k symbols)
    auto add_row = [&](const vector<u128>& data) { vector<u128> r(par.sm.k, 0); copy(data.begin(), data.end(), r.begin()); for (int x = C2; x < par.sm.k; x++) r[x] = rng.base(); smsg.push_back(r); };
    auto add_table = [&](const vector<u128>& t) { if ((int)t.size() <= C2) add_row(t); else for (size_t i = 0; i < t.size(); i += C2) add_row(vector<u128>(t.begin() + i, t.begin() + i + C2)); };
    sm.get_msg = [&](int row, u128* out) { memcpy(out, smsg[row].data(), sizeof(u128) * par.sm.k); };
    { vector<u128> sg(tau); for (int i = 0; i < tau; i++) sg[i] = w.sigma[i]; add_table(sg); }
    for (int i = 0; i < 6; i++) { vector<u128> r(C2); for (auto& x : r) x = rng.base(); add_row(r); }
    pf.root_s1 = sm.commit(0, par.c1);
    Hash stmt = in.digest();
    ch.absorb("params", par.tag()); ch.absorb("stmt", vector<u8>(stmt.begin(), stmt.end()));
    { vector<u8> b; put_hash(b, pf.root_big); put_hash(b, pf.root_s1); ch.absorb("round1", b); }
    g_time["2 commit sigma, hash statement"] += T.lap();
    vector<F> ru = ch.getF("rho_u", N), rv = ch.getF("rho_v", N), ab = ch.getF("ab", 2); F alpha = ab[0], beta = ab[1];
    Pub P = public_projection(par, in, ru, rv);
    g_time["3 project statement"] += T.lap();
    vector<F> h(tau), hh(tau);
    for (int i = 0; i < tau; i++) {
        F z = P.zpub[i];
        for (int k = 0; k < 3; k++) { const int8_t* p = w.W[k].data() + (size_t)i * N; for (int y = 0; y < N; y++) { if (p[y] == 1) z = fadd(z, P.rp[k][y]); else if (p[y] == -1) z = fsub(z, P.rp[k][y]); } }
        h[i] = fsub(fadd(z, fscale(beta, i)), alpha); hh[i] = fsub(fadd(P.zhat[i], fscale(beta, w.sigma[i])), alpha);
        if (h[i] == FZERO || hh[i] == FZERO) throw runtime_error("a denominator vanished; re-run");
    }
    vector<F> u(tau), uh(tau);
    {   // batch inversion
        auto binv = [&](const vector<F>& x, vector<F>& o) { vector<F> pre(tau + 1); pre[0] = FONE; for (int i = 0; i < tau; i++) pre[i + 1] = fmul(pre[i], x[i]); F inv = finv(pre[tau]); for (int i = tau - 1; i >= 0; i--) { o[i] = fmul(inv, pre[i]); inv = fmul(inv, x[i]); } };
        binv(h, u); binv(hh, uh);
    }
    F am[7]; for (auto& x : am) x = rng.f();                      // a_u, a_uhat, a_sigma, a_h, a_w0, a_w1, a_w2
    SCMask gA(par.dA, rng), gB(par.dB, rng), gC(par.dC, rng);
    {
        vector<u128> t0(tau), t1(tau);
        for (int i = 0; i < tau; i++) { t0[i] = u[i].a; t1[i] = u[i].b; } add_table(t0); add_table(t1);
        for (int i = 0; i < tau; i++) { t0[i] = uh[i].a; t1[i] = uh[i].b; } add_table(t0); add_table(t1);
        vector<F> me(am, am + 7); for (auto* g : {&gA, &gB, &gC}) { auto e = g->entries(); me.insert(me.end(), e.begin(), e.end()); }
        if ((int)me.size() != par.n_mask) throw runtime_error("mask table size");
        vector<u128> mr; for (auto& x : me) { mr.push_back(x.a); mr.push_back(x.b); } add_row(mr);
    }
    pf.root_s2 = sm.commit(par.c1, 4 * rs + 1);
    pf.G = {gA.total(), gB.total(), gC.total()};
    { vector<u8> b; put_hash(b, pf.root_s2); put_fs(b, pf.G); ch.absorb("round2", b); }
    g_time["4 leaves, inverses, round-2 commit"] += T.lap();
    // ---- sumcheck A
    vector<F> tc = ch.getF("tc", ell), kA = ch.getF("kA", 3); F rhoA = ch.getF("rhoA")[0];
    F bsig = fmul(beta, am[2]);
    SCOut oA = sc_prove(ch, "A", {eq_table(tc), u, h, uh, hh}, {nullptr, &am[0], &am[3], &am[1], &bsig},
                        {{kA[0], {0, 1, 2}}, {kA[1], {0, 3, 4}}, {kA[2], {1}}, {fneg(kA[2]), {3}}}, fadd(kA[0], kA[1]), ell, 3, 5, gA, rhoA);
    const vector<F>& r = oA.point; F Zr = zval(r);
    F s_val; { vector<F> sg(tau); for (int i = 0; i < tau; i++) sg[i] = fint(w.sigma[i]); s_val = fadd(mle(sg, r), fmul(am[2], Zr)); }
    pf.A = oA.msgs; pf.evalsA = {oA.finals[1], oA.finals[3], s_val, oA.finals[2]};
    { vector<u8> b; put_fs(b, pf.evalsA); ch.absorb("evalsA", b); }
    g_time["5 sumcheck A (permutation)"] += T.lap();
    // ---- sumcheck B
    F rhoB = ch.getF("rhoB")[0];
    vector<F> eqr = eq_table(r); vector<F> Wp[3];
    for (int k = 0; k < 3; k++) {
        Wp[k].assign(N, FZERO);
        for (int i = 0; i < tau; i++) { const int8_t* p = w.W[k].data() + (size_t)i * N; const F& e = eqr[i]; for (int y = 0; y < N; y++) { if (p[y] == 1) Wp[k][y] = fadd(Wp[k][y], e); else if (p[y] == -1) Wp[k][y] = fsub(Wp[k][y], e); } }
    }
    F cst = fscale(fmul(am[3], Zr), invq(N));
    F idr = FZERO; for (int b = 0; b < ell; b++) idr = fadd(idr, fscale(r[b], (u128)1 << b));
    F Sp = fadd(fsub(fsub(oA.finals[2], mle(P.zpub, r)), fmul(beta, idr)), alpha);
    SCOut oB = sc_prove(ch, "B", {P.rp[0], P.rp[1], P.rp[2], Wp[0], Wp[1], Wp[2], vector<F>(N, cst)}, vector<const F*>(7, nullptr),
                        {{FONE, {0, 3}}, {FONE, {1, 4}}, {FONE, {2, 5}}, {FONE, {6}}}, Sp, logN, 2, 2, gB, rhoB);
    pf.B = oB.msgs;
    g_time["6 sumcheck B (linear)"] += T.lap();
    // ---- sumcheck C
    vector<F> tz = ch.getF("tz", m), kC = ch.getF("kC", 3); F rhoC = ch.getF("rhoC")[0];
    SCOut oC;
    const F* aw[3] = {&am[4], &am[5], &am[6]};
    if (generic_C) {
        vector<vector<F>> tabs{eq_table(tz)};
        for (int k = 0; k < 3; k++) { vector<F> t(TN); for (long i = 0; i < TN; i++) t[i] = F{from_i8(w.W[k][i]), 0}; tabs.push_back(std::move(t)); }
        vector<Term> terms; for (int k = 0; k < 3; k++) { terms.push_back({kC[k], {0, 1 + k, 1 + k, 1 + k}}); terms.push_back({fneg(kC[k]), {0, 1 + k}}); }
        oC = sc_prove(ch, "C", std::move(tabs), {nullptr, aw[0], aw[1], aw[2]}, terms, FZERO, m, 4, 7, gC, rhoC);
    } else oC = sumcheck_C(ch, par, w, tz, kC, aw, gC, rhoC);
    pf.C = oC.msgs; pf.evalsC = {oC.finals[1], oC.finals[2], oC.finals[3]};
    { vector<u8> b; put_fs(b, pf.evalsC); ch.absorb("evalsC", b); }
    g_time["7 sumcheck C (shortness)"] += T.lap();
    // ---- restate the claims as the verifier will, then open
    ch.replay = true; Challenger rep = ch; ch.replay = false;
    Derived D = derive(par, in, stmt, pf, rep, &P, nullptr);
    vector<F> kap = ch.getF("pcs.kappa", 9);
    Slots S = compile_slots(par, D, kap);
    Mat* mats[2] = {&big, &sm}; vector<F> uv[4], mv[4]; pf.mu = FZERO;
    for (int s = 0; s < 4; s++) {
        Mat& M = *mats[s / 2];
        uv[s] = M.comb(S.rowcoef[s], S.used[s]); mv[s] = M.frow(par.maskS[s][0], par.maskS[s][1]);
        pf.mu = fadd(pf.mu, fdot(mv[s].data(), S.L[s].data(), M.mp.C));
    }
    { vector<u8> b; put_f(b, pf.mu); ch.absorb("pcs.mu", b); }
    F c = ch.getF("pcs.c")[0];
    for (int s = 0; s < 4; s++) { pf.vec[s].resize(uv[s].size()); for (size_t x = 0; x < uv[s].size(); x++) pf.vec[s][x] = fadd(mv[s][x], fmul(c, uv[s][x])); }
    for (int mi = 0; mi < 2; mi++) {
        Mat& M = *mats[mi]; vector<F> gam = ch.getF(mi == 0 ? "pcs.gamma.big" : "pcs.gamma.small", M.mp.R);
        vector<char> used(M.mp.R, 1); used[M.mp.pm0] = used[M.mp.pm1] = 0;
        vector<F> cmb = M.comb(gam, used), pm = M.frow(M.mp.pm0, M.mp.pm1);
        pf.prox[mi].resize(M.mp.k); for (int x = 0; x < M.mp.k; x++) pf.prox[mi][x] = fadd(pm[x], cmb[x]);
    }
    { vector<u8> b; for (int s = 0; s < 4; s++) put_fs(b, pf.vec[s]); for (int mi = 0; mi < 2; mi++) put_fs(b, pf.prox[mi]); ch.absorb("pcs.vec", b); }
    g_time["8 opening: combination vectors"] += T.lap();
    for (int mi = 0; mi < 2; mi++) { Mat& M = *mats[mi]; pf.cols[mi] = M.open(ch.getI(mi == 0 ? "pcs.J.big" : "pcs.J.small", M.mp.nq, M.mp.n)); }
    g_time["9 opening: columns (second encoding pass)"] += T.lap();
    return pf;
}

// ------------------------------------------------------------------ instance generation (BGV over Z_q[X]/(X^N+1))
static void gen_instance(int N, int tau, u64 seed, Instance& in, Witness& w) {
    Rng rng(seed); Ring R(N); in.N = N; in.tau = tau;
    auto tern = [&]() { vector<u128> v(N); for (auto& x : v) x = from_i8(rng.tern()); return v; };
    in.a.resize(N); for (auto& x : in.a) x = rng.base();
    vector<u128> ah = in.a; R.to(ah);
    vector<u128> s = tern(), e = tern(), sh = s; R.to(sh);
    vector<u128> bh(N); for (int i = 0; i < N; i++) bh[i] = mulq(ah[i], sh[i]);
    in.b = bh; R.from(in.b); for (int i = 0; i < N; i++) in.b[i] = addq(in.b[i], mulq(P_PLAIN, e[i]));
    bh = in.b; R.to(bh);
    auto enc0 = [&](const vector<u128>& r, const vector<u128>& e1, const vector<u128>& e2, u128* u, u128* v) {   // (a r + p e1, b r + p e2)
        vector<u128> rh = r; R.to(rh); vector<u128> x(N), y(N);
        for (int i = 0; i < N; i++) { x[i] = mulq(ah[i], rh[i]); y[i] = mulq(bh[i], rh[i]); }
        R.from(x); R.from(y);
        for (int i = 0; i < N; i++) { u[i] = addq(x[i], mulq(P_PLAIN, e1[i])); v[i] = addq(y[i], mulq(P_PLAIN, e2[i])); }
    };
    in.cin.resize((size_t)2 * tau * N); in.cout.resize((size_t)2 * tau * N);
    for (int i = 0; i < tau; i++) {
        enc0(tern(), tern(), tern(), &in.cin[(size_t)(2 * i) * N], &in.cin[(size_t)(2 * i + 1) * N]);
        for (int x = 0; x < N; x++) in.cin[(size_t)(2 * i + 1) * N + x] = addq(in.cin[(size_t)(2 * i + 1) * N + x], rng.next() & 1);
    }
    w.sigma.resize(tau); for (int i = 0; i < tau; i++) w.sigma[i] = i;
    for (int i = tau - 1; i > 0; i--) swap(w.sigma[i], w.sigma[rng.below(i + 1)]);
    vector<u32> inv(tau); for (int j = 0; j < tau; j++) inv[w.sigma[j]] = j;
    for (int k = 0; k < 3; k++) w.W[k].resize((size_t)tau * N);
    vector<u128> uu(N), vv(N);
    for (int i = 0; i < tau; i++) {
        vector<u128> t[3];
        for (int k = 0; k < 3; k++) { t[k].resize(N); for (int y = 0; y < N; y++) { int8_t v = rng.tern(); w.W[k][(size_t)i * N + y] = v; t[k][y] = from_i8(v); } }
        enc0(t[0], t[1], t[2], uu.data(), vv.data());
        size_t j = inv[i];
        for (int x = 0; x < N; x++) { in.cout[(2 * j) * N + x] = addq(in.cin[(size_t)(2 * i) * N + x], uu[x]); in.cout[(2 * j + 1) * N + x] = addq(in.cin[(size_t)(2 * i + 1) * N + x], vv[x]); }
    }
}
static vector<u8> ser_instance(const Instance& in) {
    vector<u8> o; for (int v : {in.N, in.tau}) for (int i = 3; i >= 0; i--) o.push_back((u8)(v >> (8 * i)));
    for (auto* p : {&in.a, &in.b, &in.cin, &in.cout}) for (u128 x : *p) put_base(o, x);
    return o;
}
static Instance de_instance(const vector<u8>& d) {
    Instance in; auto rd = [&](size_t p) { return ((int)d[p] << 24) | ((int)d[p + 1] << 16) | ((int)d[p + 2] << 8) | d[p + 3]; };
    in.N = rd(0); in.tau = rd(4); size_t pos = 8;
    if (d.size() != 8 + (size_t)(2 + 4 * in.tau) * in.N * EB) throw runtime_error("instance file size");
    auto take = [&](vector<u128>& v, size_t n) { v.resize(n); for (auto& x : v) { x = rd_base(&d[pos]); pos += EB; } };
    take(in.a, in.N); take(in.b, in.N); take(in.cin, (size_t)2 * in.tau * in.N); take(in.cout, (size_t)2 * in.tau * in.N);
    return in;
}
static vector<u8> read_file(const string& f) { FILE* fp = fopen(f.c_str(), "rb"); if (!fp) throw runtime_error("cannot open " + f); vector<u8> d; u8 b[1 << 16]; size_t n; while ((n = fread(b, 1, sizeof b, fp)) > 0) d.insert(d.end(), b, b + n); fclose(fp); return d; }
static void write_file(const string& f, const vector<u8>& d) { FILE* fp = fopen(f.c_str(), "wb"); if (!fp) throw runtime_error("cannot write " + f); fwrite(d.data(), 1, d.size(), fp); fclose(fp); }
static bool try_verify(const Params& par, const Instance& in, const Proof& pf, string* why = nullptr) {
    try { verify_proof(par, in, pf); return true; } catch (Reject& e) { if (why) *why = e.what(); return false; }
}

// ================================================================== decryption proof (as dec_proof.py)
// Same protocol, transcript and byte format as dec_proof.py.  The digit range check (sumcheck G) is
// specialised: the digit tables stay bytes; the first rounds accumulate eq weights per digit pattern,
// the next ones read the bytes with eq weights, and the folded tables are materialised after 8 rounds.
static void dec_size_model(int N, int tau, int base, int kd, int C1, int C2, int rate_inv, int qbits, long& field, long& opening) {
    int logN = log2i(N), ell = log2i(tau), m = logN + ell;
    long f_elems = 2 + ((long)(base + 1) * (m - 1) + 2 * base + 1) + kd + (4 * (logN - 1) + 7) + 2 + 1;
    int k1, n1, q1, k2, n2, q2; code_params(C1, rate_inv, qbits, k1, n1, q1); code_params(C2, rate_inv, qbits, k2, n2, q2);
    long R1 = (long)kd * nrows_for((long)tau * N, C1) + 6;
    field = f_elems * 2 * EB + 2 * 32;
    opening = 3L * k1 * 2 * EB + 4L * k2 * 2 * EB + (long)q1 * (R1 * EB + SALT + 32 * log2i(n1)) + (long)q2 * (11 * EB + SALT + 32 * log2i(n2));
}
static int dec_best_C1(int N, int tau, int base, int kd, int C2, int rate_inv, int qbits) {
    int best = 0; long bsz = 0;
    for (int l = 1; l <= log2i((long)tau * N); l++) {
        int C = 1 << l, k, n, q; code_params(C, rate_inv, qbits, k, n, q);
        if (n > (1 << TWO_ADICITY)) continue;
        long f, o; dec_size_model(N, tau, base, kd, C, C2, rate_inv, qbits, f, o);
        if (best == 0 || f + o < bsz) { best = C; bsz = f + o; }
    }
    return best;
}
struct DecParams {
    int N, tau, base, kdig, logN, ell, m, C1, C2, rate_inv, qbits; u64 off;
    vector<int> dG, dT; int offG, offT, n_mask, rw; MatP big, sm;
    vector<u8> tag() const {
        char b[256]; int l = snprintf(b, sizeof b, "dec|N=%d|tau=%d|base=%d|kdig=%d|C1=%d|C2=%d|rate=%d|qbits=%d|prox=%d",
                                      N, tau, base, kdig, C1, C2, rate_inv, qbits, g_prox_div);
        return vector<u8>(b, b + l);
    }
    DecParams(int N_, int tau_, int base_, int kdig_, int C1_, int C2_, int qbits_, int rate_inv_ = g_rate_inv)
        : N(N_), tau(tau_), base(base_), kdig(kdig_), rate_inv(rate_inv_), qbits(qbits_) {
        logN = log2i(N); ell = log2i(tau); m = logN + ell;
        if (base < 2 || kdig < 1) throw runtime_error("base >= 2 and kdig >= 1");
        u128 B = 1; for (int i = 0; i < kdig; i++) { B *= base; if (B > ((u128)1 << 62)) throw runtime_error("base^kdig too large"); }
        off = (u64)(B / 2);
        dG = sc_degs(m, base + 1, 2 * base + 1); dT = sc_degs(logN, 4, 7);
        offG = kdig + 2; offT = offG + 1 + sumv(dG); n_mask = offT + 1 + sumv(dT);
        int mx = max(N, 2 * n_mask), c2min = 1; while (c2min < mx) c2min <<= 1;
        C2 = C2_ ? C2_ : c2min; if (C2 < c2min) throw runtime_error("C2 too small");
        C1 = C1_ ? C1_ : dec_best_C1(N, tau, base, kdig, C2, rate_inv, qbits);
        rw = nrows_for((long)tau * N, C1);
        big = make_matp(C1, rate_inv, qbits, {kdig * rw + 6}, kdig * rw + 4, kdig * rw + 5);
        sm = make_matp(C2, rate_inv, qbits, {11}, 9, 10);
    }
};
// slots, in sorted order of their names: S1 S2 (big), Se Sm Ss (small)
enum { S1 = 0, S2 = 1, SE = 2, SM = 3, SS = 4 };
static const int DSLOT_MAT[5] = {0, 0, 1, 1, 1};
static const bool DSLOT_TENSOR[5] = {true, true, false, false, false};
static void dslot_mask(const DecParams& par, int sid, int& a, int& b) {
    int kr = par.kdig * par.rw;
    switch (sid) { case S1: a = kr; b = kr + 1; break; case S2: a = kr + 2; b = kr + 3; break;
                   case SS: a = 3; b = 4; break; case SE: a = 5; b = 6; break; default: a = 7; b = 8; }
}
struct DecStmt {
    int N, tau; vector<u128> a, b, us, ts;                        // us[i*N + x], ts[i*N + x]
    Hash digest() const {
        SHA256_CTX c; SHA256_Init(&c); vector<u8> buf((size_t)N * EB);
        auto feed = [&](const u128* p) { for (int x = 0; x < N; x++) wr_base(&buf[(size_t)x * EB], p[x]); SHA256_Update(&c, buf.data(), buf.size()); };
        feed(a.data()); feed(b.data());
        for (int i = 0; i < tau; i++) feed(&us[(size_t)i * N]);
        for (int i = 0; i < tau; i++) feed(&ts[(size_t)i * N]);
        Hash h; SHA256_Final(h.data(), &c); return h;
    }
};
static vector<u8> ser_dstmt(const DecStmt& st) {
    vector<u8> o; for (int v : {st.N, st.tau}) for (int i = 3; i >= 0; i--) o.push_back((u8)(v >> (8 * i)));
    for (auto* p : {&st.a, &st.b, &st.us, &st.ts}) for (u128 x : *p) put_base(o, x);
    return o;
}
static DecStmt de_dstmt(const vector<u8>& d) {
    if (d.size() < 8) throw Reject("statement too short");
    DecStmt st; auto rd = [&](size_t p) { return ((int)d[p] << 24) | ((int)d[p + 1] << 16) | ((int)d[p + 2] << 8) | d[p + 3]; };
    st.N = rd(0); st.tau = rd(4); size_t pos = 8;
    if (d.size() != 8 + (size_t)(2 + 2 * st.tau) * st.N * EB) throw Reject("statement: wrong length");
    auto take = [&](vector<u128>& v, size_t n) { v.resize(n); for (auto& x : v) { x = rd_base(&d[pos]); pos += EB; if (x >= Q) throw Reject("statement: entry not reduced"); } };
    take(st.a, st.N); take(st.b, st.N); take(st.us, (size_t)st.tau * st.N); take(st.ts, (size_t)st.tau * st.N);
    return st;
}
struct DecProof {
    Hash rb, rs; vector<F> G; vector<vector<F>> scG, scT; vector<F> evG, evT; F mu;
    vector<F> vec[5], prox[2]; vector<vector<ColB>> cols[2];
};
static vector<u8> ser_dproof(const DecProof& p) {
    vector<u8> o; put_hash(o, p.rb); put_hash(o, p.rs); put_fs(o, p.G);
    for (auto& r : p.scG) put_fs(o, r); put_fs(o, p.evG);
    for (auto& r : p.scT) put_fs(o, r); put_fs(o, p.evT); put_f(o, p.mu);
    for (int s = 0; s < 5; s++) put_fs(o, p.vec[s]); for (int mi = 0; mi < 2; mi++) put_fs(o, p.prox[mi]);
    for (int mi = 0; mi < 2; mi++) for (auto& q : p.cols[mi]) for (auto& cb : q) {
        for (u128 x : cb.e) put_base(o, x);
        o.insert(o.end(), cb.salt.begin(), cb.salt.end()); for (auto& h : cb.path) put_hash(o, h);
    }
    return o;
}
static DecProof de_dproof(const DecParams& par, const vector<u8>& d) {
    size_t pos = 0;
    auto take = [&](size_t n) { if (pos + n > d.size()) throw Reject("proof too short"); pos += n; return &d[pos - n]; };
    auto base = [&]() { u128 v = rd_base(take(EB)); if (v >= Q) throw Reject("malformed field element"); return v; };
    auto f = [&]() { F x; x.a = base(); x.b = base(); return x; };
    auto fs = [&](int n) { vector<F> v(n); for (auto& x : v) x = f(); return v; };
    auto hs = [&]() { Hash h; memcpy(h.data(), take(32), 32); return h; };
    DecProof p; p.rb = hs(); p.rs = hs(); p.G = fs(2);
    for (int dd : par.dG) p.scG.push_back(fs(dd)); p.evG = fs(par.kdig);
    for (int dd : par.dT) p.scT.push_back(fs(dd)); p.evT = fs(2); p.mu = f();
    for (int s = 0; s < 5; s++) p.vec[s] = fs(DSLOT_MAT[s] == 0 ? par.big.k : par.sm.k);
    p.prox[0] = fs(par.big.k); p.prox[1] = fs(par.sm.k);
    const MatP* mp[2] = {&par.big, &par.sm};
    for (int mi = 0; mi < 2; mi++) {
        p.cols[mi].resize(mp[mi]->nq);
        for (auto& q : p.cols[mi]) for (int cnt : mp[mi]->batch_rows) {
            ColB cb; cb.e.resize(cnt); for (auto& x : cb.e) x = base();
            memcpy(cb.salt.data(), take(SALT), SALT); for (int l = 0; l < mp[mi]->logn; l++) cb.path.push_back(hs());
            q.push_back(std::move(cb));
        }
    }
    if (pos != d.size()) throw Reject("trailing bytes");
    return p;
}

// ------------------------------------------------------------------ generic opening of linear claims (fp_core._slots_compile, pcs_open_*)
struct CTerm { int sid, row; F coef; vector<pair<int, F>> lv; };      // lv empty for tensor slots
struct CClaim { F value; vector<CTerm> terms; };
struct GSlots { vector<F> rowcoef[5]; vector<char> used[5]; vector<F> L[5]; F V; };
static GSlots compile_gslots(const DecParams& par, const vector<F> lov[5], const vector<CClaim>& claims, const vector<F>& kap) {
    GSlots S; S.V = FZERO;
    for (int s = 0; s < 5; s++) {
        const MatP& M = DSLOT_MAT[s] == 0 ? par.big : par.sm;
        S.rowcoef[s].assign(M.R, FZERO); S.used[s].assign(M.R, 0);
        S.L[s] = DSLOT_TENSOR[s] ? lov[s] : vector<F>(M.C, FZERO);
    }
    for (size_t i = 0; i < claims.size(); i++) {
        S.V = fadd(S.V, fmul(kap[i], claims[i].value));
        for (auto& t : claims[i].terms) {
            F kc = fmul(kap[i], t.coef);
            if (DSLOT_TENSOR[t.sid]) { S.rowcoef[t.sid][t.row] = fadd(S.rowcoef[t.sid][t.row], kc); S.used[t.sid][t.row] = 1; }
            else {
                S.rowcoef[t.sid][t.row] = FONE; S.used[t.sid][t.row] = 1;
                for (auto& [pos, c] : t.lv) S.L[t.sid][pos] = fadd(S.L[t.sid][pos], fmul(kc, c));
            }
        }
    }
    return S;
}

// w[x'] = sum_x e[x] coeff_x(v X^{x'}) in Z_q[X]/(X^N+1) = coeff_{x'}(v* e), v* the adjoint; v = v0 + t v1 with v1 optional
static vector<F> tshift(const Ring& R, const vector<u128>& v0, const vector<u128>* v1, const vector<F>& e) {
    int N = R.N;
    auto star = [&](const vector<u128>& p) { vector<u128> t(N); t[0] = p[0]; for (int j = 1; j < N; j++) t[j] = negq(p[N - j]); R.to(t); return t; };
    vector<u128> e0(N), e1(N); for (int x = 0; x < N; x++) { e0[x] = e[x].a; e1[x] = e[x].b; }
    R.to(e0); R.to(e1);
    vector<u128> a0 = star(v0), r0(N), r1(N);
    if (v1) {
        vector<u128> a1 = star(*v1);
        for (int i = 0; i < N; i++) {
            r0[i] = addq(mulq(a0[i], e0[i]), mulq(3, mulq(a1[i], e1[i])));
            r1[i] = addq(mulq(a0[i], e1[i]), mulq(a1[i], e0[i]));
        }
    } else for (int i = 0; i < N; i++) { r0[i] = mulq(a0[i], e0[i]); r1[i] = mulq(a0[i], e1[i]); }
    R.from(r0); R.from(r1);
    vector<F> w(N); for (int i = 0; i < N; i++) w[i] = F{r0[i], r1[i]}; return w;
}

// the verifier's claims (dec_derive)
struct DecDerived { vector<F> lov[5]; vector<CClaim> claims; };
static DecDerived dec_derive(const DecParams& par, const DecStmt& st, const DecProof& pf, Challenger& ch) {
    const int N = par.N, tau = par.tau, ell = par.ell, logN = par.logN, m = par.m, base = par.base, kd = par.kdig;
    if (pf.G.size() != 2 || (int)pf.evG.size() != kd || pf.evT.size() != 2) throw Reject("malformed proof");
    ch.absorb("params", par.tag()); { Hash h = st.digest(); ch.absorb("stmt", vector<u8>(h.begin(), h.end())); }
    { vector<u8> b; put_hash(b, pf.rb); put_hash(b, pf.rs); put_fs(b, pf.G); ch.absorb("round1", b); }
    vector<F> th = ch.getF("theta", ell), th1 = ch.getF("theta1", logN), th2 = ch.getF("theta2", logN);
    vector<F> eqt = eq_table(th), eq1 = eq_table(th1), eq2 = eq_table(th2);
    vector<F> Tc(N, FZERO); vector<u128> U0(N, 0), U1(N, 0);
    for (int i = 0; i < tau; i++) for (int x = 0; x < N; x++) {
        Tc[x] = fadd(Tc[x], fscale(eqt[i], st.ts[(size_t)i * N + x]));
        F u = fscale(eqt[i], st.us[(size_t)i * N + x]); U0[x] = addq(U0[x], u.a); U1[x] = addq(U1[x], u.b);
    }
    F valD = fadd(fdot(eq1.data(), Tc.data(), N), fint(0)); valD = fadd(valD, F{(u128)P_PLAIN * par.off % Q, 0});
    Ring R(N);
    vector<F> w_s = tshift(R, U0, &U1, eq1), w_a = tshift(R, st.a, nullptr, eq2);
    F valK = fdot_base(eq2.data(), st.b.data(), N);
    vector<F> tz = ch.getF("tz", m), kG = ch.getF("kG", kd); F rhoG = ch.getF("rhoG")[0];
    auto [rz, clG] = sc_verify(ch, "G", pf.scG, fmul(rhoG, pf.G[0]), m, base + 1, 2 * base + 1);
    { vector<u8> b; put_fs(b, pf.evG); ch.absorb("evalsG", b); }
    F acc = FZERO;
    for (int d = 0; d < kd; d++) { F pr = FONE; for (int v = 0; v < base; v++) pr = fmul(pr, fsub(pf.evG[d], fint(v))); acc = fadd(acc, fmul(kG[d], pr)); }
    if (rhoG == FZERO) throw Reject("degenerate challenge");
    F gvalG = fmul(fsub(clG, fmul(eq_eval(tz, rz), acc)), finv(rhoG));
    vector<F> tt = ch.getF("tt", logN), kT = ch.getF("kT", 2); F rhoT = ch.getF("rhoT")[0];
    auto [rt, clT] = sc_verify(ch, "T", pf.scT, fmul(rhoT, pf.G[1]), logN, 4, 7);
    F sz = pf.evT[0], ez = pf.evT[1]; { vector<u8> b; put_fs(b, pf.evT); ch.absorb("evalsT", b); }
    auto cube = [](const F& w) { return fsub(fmul(fmul(w, w), w), w); };
    if (rhoT == FZERO) throw Reject("degenerate challenge");
    F gvalT = fmul(fsub(clT, fmul(eq_eval(tt, rt), fadd(fmul(kT[0], cube(sz)), fmul(kT[1], cube(ez))))), finv(rhoT));
    // claims
    const int C1 = par.C1, rw = par.rw; long TN = (long)tau * N;
    vector<F> ptD = th1; ptD.insert(ptD.end(), th.begin(), th.end());
    DecDerived D; D.lov[S1] = lo_vec(ptD, C1, TN); D.lov[S2] = lo_vec(rz, C1, TN);
    vector<F> hiD = hi_coefs(ptD, C1, TN), hiz = hi_coefs(rz, C1, TN);
    auto tab = [&](vector<CTerm>& out, int sid, int start, const vector<F>& hi, const F& coef) {
        for (size_t i = 0; i < hi.size(); i++) out.push_back(CTerm{sid, start + (int)i, fmul(coef, hi[i]), {}});
    };
    auto listlv = [](const vector<F>& v) { vector<pair<int, F>> o; for (size_t i = 0; i < v.size(); i++) o.push_back({(int)i, v[i]}); return o; };
    auto unitlv = [](int e) { return vector<pair<int, F>>{{2 * e, FONE}, {2 * e + 1, FT}}; };
    auto gfunlv = [](int off, const vector<F>& cf) { vector<pair<int, F>> o; for (size_t i = 0; i < cf.size(); i++) { o.push_back({2 * (off + (int)i), cf[i]}); o.push_back({2 * (off + (int)i) + 1, fmul(cf[i], FT)}); } return o; };
    const int mr = 2, row_s = 0, row_e = 1; F Zrz = zval(rz), Zrt = zval(rt); vector<F> eqrt = eq_table(rt);
    { CClaim c{valD, {CTerm{SS, row_s, FONE, listlv(w_s)}}}; u128 pw = 1;
      for (int d = 0; d < kd; d++) { tab(c.terms, S1, d * rw, hiD, F{mulq(P_PLAIN, pw), 0}); pw = mulq(pw, base); }
      D.claims.push_back(c); }
    D.claims.push_back(CClaim{valK, {CTerm{SS, row_s, FONE, listlv(w_a)}, CTerm{SE, row_e, fint(P_PLAIN), listlv(eq2)}}});
    for (int d = 0; d < kd; d++) { CClaim c{pf.evG[d], {}}; tab(c.terms, S2, d * rw, hiz, FONE); c.terms.push_back(CTerm{SM, mr, Zrz, unitlv(d)}); D.claims.push_back(c); }
    D.claims.push_back(CClaim{sz, {CTerm{SS, row_s, FONE, listlv(eqrt)}, CTerm{SM, mr, Zrt, unitlv(kd)}}});
    D.claims.push_back(CClaim{ez, {CTerm{SE, row_e, FONE, listlv(eqrt)}, CTerm{SM, mr, Zrt, unitlv(kd + 1)}}});
    D.claims.push_back(CClaim{gvalG, {CTerm{SM, mr, FONE, gfunlv(par.offG, SCMask::functional(par.dG, rz))}}});
    D.claims.push_back(CClaim{gvalT, {CTerm{SM, mr, FONE, gfunlv(par.offT, SCMask::functional(par.dT, rt))}}});
    return D;
}

static void dec_verify(const DecParams& par, const DecStmt& st, const DecProof& pf) {
    if (st.N != par.N || st.tau != par.tau) throw Reject("statement does not match N, tau");
    Challenger ch("dec");
    DecDerived D = dec_derive(par, st, pf, ch);
    vector<F> kap = ch.getF("pcs.kappa", (int)D.claims.size());
    GSlots S = compile_gslots(par, D.lov, D.claims, kap);
    { vector<u8> b; put_f(b, pf.mu); ch.absorb("pcs.mu", b); }
    F c = ch.getF("pcs.c")[0];
    const MatP* mp[2] = {&par.big, &par.sm};
    for (int s = 0; s < 5; s++) if ((int)pf.vec[s].size() != mp[DSLOT_MAT[s]]->k) throw Reject("opening: vector length");
    vector<F> gam[2];
    for (int mi = 0; mi < 2; mi++) { if ((int)pf.prox[mi].size() != mp[mi]->k) throw Reject("opening: vector length"); gam[mi] = ch.getF(mi == 0 ? "pcs.gamma.big" : "pcs.gamma.small", mp[mi]->R); }
    { vector<u8> b; for (int s = 0; s < 5; s++) put_fs(b, pf.vec[s]); for (int mi = 0; mi < 2; mi++) put_fs(b, pf.prox[mi]); ch.absorb("pcs.vec", b); }
    F lhs = FZERO;
    for (int s = 0; s < 5; s++) lhs = fadd(lhs, fdot(pf.vec[s].data(), S.L[s].data(), mp[DSLOT_MAT[s]]->C));
    if (lhs != fadd(pf.mu, fmul(c, S.V))) throw Reject("opening: claimed values");
    const Hash* roots[2] = {&pf.rb, &pf.rs};
    for (int mi = 0; mi < 2; mi++) {
        const MatP& M = *mp[mi]; NTT ntt(M.n, M.w);
        vector<u32> J = ch.getI(mi == 0 ? "pcs.J.big" : "pcs.J.small", M.nq, M.n);
        vector<u128> p0, p1; encode_ext(M, ntt, pf.prox[mi], p0, p1);
        vector<int> sids; for (int s = 0; s < 5; s++) if (DSLOT_MAT[s] == mi) sids.push_back(s);
        vector<vector<u128>> v0(5), v1(5); for (int s : sids) encode_ext(M, ntt, pf.vec[s], v0[s], v1[s]);
        if ((int)pf.cols[mi].size() != M.nq) throw Reject("opening: number of columns");
        vector<u128> col(M.R);
        for (int q = 0; q < M.nq; q++) {
            u32 j = J[q]; const auto& pb = pf.cols[mi][q];
            if (pb.size() != M.batch_rows.size()) throw Reject("opening: batches");
            int at = 0;
            for (size_t b = 0; b < pb.size(); b++) {
                if ((int)pb[b].e.size() != M.batch_rows[b] || (int)pb[b].path.size() != M.logn) throw Reject("opening: malformed column");
                for (u128 x : pb[b].e) { if (x >= Q) throw Reject("opening: malformed column"); col[at++] = x; }
                if (merkle_root_from(leaf_hash(pb[b].salt.data(), pb[b].e), j, pb[b].path) != *roots[mi]) throw Reject("opening: Merkle path");
            }
            F sacc{col[M.pm0], col[M.pm1]};
            for (int i = 0; i < M.R; i++) if (i != M.pm0 && i != M.pm1) acc_small(sacc, gam[mi][i], col[i]);
            if (sacc != F{p0[j], p1[j]}) throw Reject("opening: proximity vector");
            for (int s : sids) {
                F a = FZERO; for (int i = 0; i < M.R; i++) if (S.used[s][i]) acc_small(a, S.rowcoef[s][i], col[i]);
                F cmb = fmul(c, a); int ma, mb; dslot_mask(par, s, ma, mb);
                if (F{addq(col[ma], cmb.a), addq(col[mb], cmb.b)} != F{v0[s][j], v1[s][j]}) throw Reject("opening: combination vector");
            }
        }
    }
}
static bool try_dverify(const DecParams& par, const DecStmt& st, const DecProof& pf, string* why = nullptr) {
    try { dec_verify(par, st, pf); return true; } catch (Reject& e) { if (why) *why = e.what(); return false; }
}

// ------------------------------------------------------------------ the digit sumcheck G, specialised
// Summand eq(tz, x) * sum_d kG[d] * P(D_d(x)), P(y) = prod_{v<base} (y - v); D_d are bytes.
static vector<Term> g_terms(const vector<F>& kG, int base) {
    vector<Term> terms;
    for (size_t d = 0; d < kG.size(); d++) {
        Term t; t.coef = kG[d]; t.fac = {0}; t.sh = {0};
        for (int v = 0; v < base; v++) { t.fac.push_back(1 + (int)d); t.sh.push_back((u64)v); }
        terms.push_back(t);
    }
    return terms;
}
static SCOut sumcheck_G(Challenger& ch, const DecParams& par, const vector<vector<u8>>& D, const vector<F>& tz, const vector<F>& kG,
                        const vector<F>& ad, const SCMask& g, const F& rho_g) {
    const int m = par.m, base = par.base, kd = par.kdig, dg = base + 1; const size_t n = (size_t)1 << m;
    SCOut o; o.claim = fmul(rho_g, g.total());
    vector<Term> terms = g_terms(kG, base);
    vector<const F*> tm{nullptr}; for (auto& a : ad) tm.push_back(&a);
    if (m == 1) {
        vector<vector<F>> tabs{eq_table(tz)};
        for (int d = 0; d < kd; d++) { vector<F> t(n); for (size_t i = 0; i < n; i++) t[i] = fint(D[d][i]); tabs.push_back(t); }
        sc_last_round(ch, "G", 0, tabs, tm, terms, 2 * base + 1, g, rho_g, o); return o;
    }
    const int KS = min(m - 1, 8);
    auto P = [&](const F& y) { F p = y; for (int v = 1; v < base; v++) p = fmul(p, fsub(y, fint(v))); return p; };
    F Ej = FONE; vector<F> E{FONE}; vector<vector<F>> T(kd);
    vector<F> cs(base + 1); for (int c = 0; c <= base; c++) cs[c] = fint(c);
    for (int j = 0; j < m - 1; j++) {
        const size_t blk = (size_t)1 << (j + 1), hb = blk / 2, cnt = n >> (j + 1);
        vector<F> eqr = eq_table(tz.data() + j + 1, m - j - 1);
        vector<F> t(base + 1, FZERO);
        double npd = pow((double)base, (double)blk);
        if (j < KS && npd <= 65536.0) {                          // buckets: one field addition per position and digit
            size_t npat = (size_t)npd;
            vector<vector<F>> LUT(base + 1, vector<F>(npat));
            for (size_t pat = 0; pat < npat; pat++) {
                size_t x = pat; F A = FZERO, B = FZERO;
                for (size_t p = 0; p < blk; p++) { u64 dig = x % base; x /= base; F& tgt = p < hb ? A : B; tgt = fadd(tgt, fscale(E[p % hb], dig)); }
                F df = fsub(B, A), y = A;
                for (int c = 0; c <= base; c++) { LUT[c][pat] = P(y); y = fadd(y, df); }
            }
            vector<size_t> pw(blk); pw[0] = 1; for (size_t p = 1; p < blk; p++) pw[p] = pw[p - 1] * base;
            for (int d = 0; d < kd; d++) {
                vector<F> W(npat, FZERO); const u8* Dd = D[d].data();
                for (size_t i = 0; i < cnt; i++) { size_t pat = 0; const u8* q = Dd + i * blk; for (size_t p = 0; p < blk; p++) pat += pw[p] * q[p]; W[pat] = fadd(W[pat], eqr[i]); }
                for (int c = 0; c <= base; c++) { F s = FZERO; for (size_t pat = 0; pat < npat; pat++) if (W[pat] != FZERO) s = fadd(s, fmul(W[pat], LUT[c][pat])); t[c] = fadd(t[c], fmul(kG[d], s)); }
            }
        } else {
            vector<vector<F>> Em;                                 // E[p] * v for digits v (on-the-fly rounds)
            if (j < KS) { Em.assign(hb, vector<F>(base)); for (size_t p = 0; p < hb; p++) for (int v = 0; v < base; v++) Em[p][v] = fscale(E[p], v); }
            vector<F> sc(base + 1);
            for (size_t i = 0; i < cnt; i++) {
                fill(sc.begin(), sc.end(), FZERO);
                for (int d = 0; d < kd; d++) {
                    F A = FZERO, B = FZERO;
                    if (j < KS) { const u8* q = D[d].data() + i * blk; for (size_t p = 0; p < hb; p++) { if (q[p]) A = fadd(A, Em[p][q[p]]); if (q[hb + p]) B = fadd(B, Em[p][q[hb + p]]); } }
                    else { A = T[d][2 * i]; B = T[d][2 * i + 1]; }
                    F df = fsub(B, A), y = A;
                    for (int c = 0; c <= base; c++) { sc[c] = fadd(sc[c], fmul(kG[d], P(y))); y = fadd(y, df); }
                }
                for (int c = 0; c <= base; c++) t[c] = fadd(t[c], fmul(eqr[i], sc[c]));
            }
        }
        // round polynomial: E_j * l_j(X) * t(X), t of degree base
        F l0 = fsub(FONE, tz[j]), l1 = tz[j], dl = fsub(l1, l0);
        vector<F> tv = t; tv.push_back(interp(t, fint(base + 1)));
        vector<F> vals(dg + 1); F lc = l0;
        for (int c = 0; c <= dg; c++) { vals[c] = fmul(Ej, fmul(lc, tv[c])); lc = fadd(lc, dl); }
        F r = sc_finish_round(ch, "G", j, vals, g, rho_g, o);
        Ej = fmul(Ej, fadd(l0, fmul(r, dl)));
        if (j + 1 <= KS) { size_t sz = E.size(); E.resize(2 * sz); F om = fsub(FONE, r); for (size_t b = 0; b < sz; b++) { E[sz + b] = fmul(E[b], r); E[b] = fmul(E[b], om); } }
        if (j + 1 == KS) {
            size_t c2 = n >> KS, bsz = (size_t)1 << KS;
            vector<vector<F>> Em(bsz, vector<F>(base)); for (size_t p = 0; p < bsz; p++) for (int v = 0; v < base; v++) Em[p][v] = fscale(E[p], v);
            for (int d = 0; d < kd; d++) {
                T[d].assign(c2, FZERO); const u8* q = D[d].data();
                for (size_t i = 0; i < c2; i++) { F a = FZERO; for (size_t p = 0; p < bsz; p++) { u8 v = q[i * bsz + p]; if (v) a = fadd(a, Em[p][v]); } T[d][i] = a; }
            }
        } else if (j + 1 > KS) for (int d = 0; d < kd; d++) fold(T[d], r);
    }
    vector<vector<F>> tabs{vector<F>{fmul(Ej, fsub(FONE, tz[m - 1])), fmul(Ej, tz[m - 1])}};
    for (int d = 0; d < kd; d++) tabs.push_back(T[d]);
    sc_last_round(ch, "G", m - 1, tabs, tm, terms, 2 * base + 1, g, rho_g, o);
    return o;
}

// ------------------------------------------------------------------ the decryption prover
static DecProof dec_prove(const DecParams& par, const DecStmt& st, const vector<int8_t>& s, const vector<int8_t>& e,
                          const vector<vector<u8>>& D, Rng& rng, bool generic_G = false) {
    const int N = par.N, tau = par.tau, ell = par.ell, logN = par.logN, m = par.m, base = par.base, kd = par.kdig;
    const int C1 = par.C1, C2 = par.C2, rw = par.rw; const long TN = (long)tau * N;
    DecProof pf; Timer TT; Challenger ch("dec");
    // big matrix: digit rows read from the byte tables, then three random F-rows (two Z_q rows each)
    Mat big(par.big, &rng);
    vector<vector<u128>> bpad(kd * rw, vector<u128>(par.big.nq)); for (auto& r : bpad) for (auto& x : r) x = rng.base();
    vector<vector<u128>> bmask(6, vector<u128>(par.big.k)); for (auto& r : bmask) for (auto& x : r) x = rng.base();
    big.get_msg = [&](int row, u128* out) {
        if (row >= kd * rw) { memcpy(out, bmask[row - kd * rw].data(), sizeof(u128) * par.big.k); return; }
        const u8* p = D[row / rw].data() + (size_t)(row % rw) * C1; long len = min<long>(C1, TN);
        for (long x = 0; x < len; x++) out[x] = p[x];
        for (long x = len; x < C1; x++) out[x] = 0;
        memcpy(out + C1, bpad[row].data(), sizeof(u128) * par.big.nq);
    };
    pf.rb = big.commit(0, par.big.R);
    g_time["1 commit digits (encode + hash)"] += TT.lap();
    vector<F> ad(kd); for (auto& x : ad) x = rng.f(); F as_ = rng.f(), ae_ = rng.f();
    SCMask gG(par.dG, rng), gT(par.dT, rng);
    Mat sm(par.sm, &rng); vector<vector<u128>> smsg;
    auto add_row = [&](const vector<u128>& data) { vector<u128> r(par.sm.k, 0); copy(data.begin(), data.end(), r.begin()); for (int x = C2; x < par.sm.k; x++) r[x] = rng.base(); smsg.push_back(r); };
    sm.get_msg = [&](int row, u128* out) { memcpy(out, smsg[row].data(), sizeof(u128) * par.sm.k); };
    { vector<u128> r(N); for (int x = 0; x < N; x++) r[x] = from_i8(s[x]); add_row(r); for (int x = 0; x < N; x++) r[x] = from_i8(e[x]); add_row(r); }
    {
        vector<F> me = ad; me.push_back(as_); me.push_back(ae_);
        for (auto* gg : {&gG, &gT}) { auto en = gg->entries(); me.insert(me.end(), en.begin(), en.end()); }
        if ((int)me.size() != par.n_mask) throw runtime_error("mask table size");
        vector<u128> mr; for (auto& x : me) { mr.push_back(x.a); mr.push_back(x.b); } add_row(mr);
    }
    for (int i = 0; i < 8; i++) { vector<u128> r(C2); for (auto& x : r) x = rng.base(); add_row(r); }
    pf.rs = sm.commit(0, 11);
    pf.G = {gG.total(), gT.total()};
    Hash stmt = st.digest();
    ch.absorb("params", par.tag()); ch.absorb("stmt", vector<u8>(stmt.begin(), stmt.end()));
    { vector<u8> b; put_hash(b, pf.rb); put_hash(b, pf.rs); put_fs(b, pf.G); ch.absorb("round1", b); }
    ch.getF("theta", ell); ch.getF("theta1", logN); ch.getF("theta2", logN);
    g_time["2 commit key share and masks, hash statement"] += TT.lap();
    // digit range check
    vector<F> tz = ch.getF("tz", m), kG = ch.getF("kG", kd); F rhoG = ch.getF("rhoG")[0];
    SCOut oG;
    if (generic_G) {
        vector<vector<F>> tabs{eq_table(tz)};
        for (int d = 0; d < kd; d++) { vector<F> t(TN); for (long i = 0; i < TN; i++) t[i] = fint(D[d][i]); tabs.push_back(std::move(t)); }
        vector<const F*> tm{nullptr}; for (auto& a : ad) tm.push_back(&a);
        oG = sc_prove(ch, "G", std::move(tabs), tm, g_terms(kG, base), FZERO, m, base + 1, 2 * base + 1, gG, rhoG);
    } else oG = sumcheck_G(ch, par, D, tz, kG, ad, gG, rhoG);
    pf.scG = oG.msgs; pf.evG.assign(oG.finals.begin() + 1, oG.finals.end());
    { vector<u8> b; put_fs(b, pf.evG); ch.absorb("evalsG", b); }
    g_time["3 sumcheck G (digits)"] += TT.lap();
    // ternary key share
    vector<F> tt = ch.getF("tt", logN), kT = ch.getF("kT", 2); F rhoT = ch.getF("rhoT")[0];
    {
        vector<F> sF(N), eF(N); for (int x = 0; x < N; x++) { sF[x] = F{from_i8(s[x]), 0}; eF[x] = F{from_i8(e[x]), 0}; }
        SCOut oT = sc_prove(ch, "T", {eq_table(tt), sF, eF}, {nullptr, &as_, &ae_},
                            {{kT[0], {0, 1, 1, 1}}, {fneg(kT[0]), {0, 1}}, {kT[1], {0, 2, 2, 2}}, {fneg(kT[1]), {0, 2}}}, FZERO, logN, 4, 7, gT, rhoT);
        pf.scT = oT.msgs; pf.evT = {oT.finals[1], oT.finals[2]};
    }
    { vector<u8> b; put_fs(b, pf.evT); ch.absorb("evalsT", b); }
    g_time["4 sumcheck T (key share)"] += TT.lap();
    // restate the claims as the verifier will, then open
    ch.replay = true; Challenger rep = ch; ch.replay = false;
    DecDerived DD = dec_derive(par, st, pf, rep);
    g_time["5 claims (as the verifier)"] += TT.lap();
    vector<F> kap = ch.getF("pcs.kappa", (int)DD.claims.size());
    GSlots S = compile_gslots(par, DD.lov, DD.claims, kap);
    Mat* mats[2] = {&big, &sm}; vector<F> uv[5], mv[5]; pf.mu = FZERO;
    for (int sid = 0; sid < 5; sid++) {
        Mat& M = *mats[DSLOT_MAT[sid]]; int ma, mb; dslot_mask(par, sid, ma, mb);
        uv[sid] = M.comb(S.rowcoef[sid], S.used[sid]); mv[sid] = M.frow(ma, mb);
        pf.mu = fadd(pf.mu, fdot(mv[sid].data(), S.L[sid].data(), M.mp.C));
    }
    { vector<u8> b; put_f(b, pf.mu); ch.absorb("pcs.mu", b); }
    F c = ch.getF("pcs.c")[0];
    for (int sid = 0; sid < 5; sid++) { pf.vec[sid].resize(uv[sid].size()); for (size_t x = 0; x < uv[sid].size(); x++) pf.vec[sid][x] = fadd(mv[sid][x], fmul(c, uv[sid][x])); }
    for (int mi = 0; mi < 2; mi++) {
        Mat& M = *mats[mi]; vector<F> gam = ch.getF(mi == 0 ? "pcs.gamma.big" : "pcs.gamma.small", M.mp.R);
        vector<char> used(M.mp.R, 1); used[M.mp.pm0] = used[M.mp.pm1] = 0;
        vector<F> cmb = M.comb(gam, used), pm = M.frow(M.mp.pm0, M.mp.pm1);
        pf.prox[mi].resize(M.mp.k); for (int x = 0; x < M.mp.k; x++) pf.prox[mi][x] = fadd(pm[x], cmb[x]);
    }
    { vector<u8> b; for (int sid = 0; sid < 5; sid++) put_fs(b, pf.vec[sid]); for (int mi = 0; mi < 2; mi++) put_fs(b, pf.prox[mi]); ch.absorb("pcs.vec", b); }
    g_time["6 opening: combination vectors"] += TT.lap();
    for (int mi = 0; mi < 2; mi++) { Mat& M = *mats[mi]; pf.cols[mi] = M.open(ch.getI(mi == 0 ? "pcs.J.big" : "pcs.J.small", M.mp.nq, M.mp.n)); }
    g_time["7 opening: columns (second encoding pass)"] += TT.lap();
    return pf;
}

// instance: key share b = a s + p e, random first ciphertext components u_i, shares t_i = s u_i + p E_i
static void gen_dec(const DecParams& par, u64 seed, DecStmt& st, vector<int8_t>& s, vector<int8_t>& e, vector<vector<u8>>& D) {
    Rng rng(seed); const int N = par.N, tau = par.tau; Ring R(N); st.N = N; st.tau = tau;
    st.a.resize(N); for (auto& x : st.a) x = rng.base();
    s.resize(N); e.resize(N); for (auto& x : s) x = rng.tern(); for (auto& x : e) x = rng.tern();
    vector<u128> sh(N); for (int x = 0; x < N; x++) sh[x] = from_i8(s[x]); R.to(sh);
    vector<u128> ah = st.a; R.to(ah); st.b.resize(N);
    for (int x = 0; x < N; x++) st.b[x] = mulq(ah[x], sh[x]);
    R.from(st.b); for (int x = 0; x < N; x++) st.b[x] = addq(st.b[x], mulq(P_PLAIN, from_i8(e[x])));
    st.us.resize((size_t)tau * N); st.ts.resize((size_t)tau * N);
    D.assign(par.kdig, vector<u8>((size_t)tau * N));
    vector<u128> uh(N);
    for (int i = 0; i < tau; i++) {
        for (int x = 0; x < N; x++) uh[x] = st.us[(size_t)i * N + x] = rng.base();
        R.to(uh); for (int x = 0; x < N; x++) uh[x] = mulq(uh[x], sh[x]); R.from(uh);
        for (int x = 0; x < N; x++) {
            u64 v = rng.below(2 * par.off);                        // E + off, E in [-off, off)
            long long E = (long long)v - (long long)par.off;
            u128 pE = E >= 0 ? mulq(P_PLAIN, (u128)E) : negq(mulq(P_PLAIN, (u128)(-E)));
            st.ts[(size_t)i * N + x] = addq(uh[x], pE);
            for (int d = 0; d < par.kdig; d++) { D[d][x + (size_t)N * i] = (u8)(v % par.base); v /= par.base; }
        }
    }
}

int main(int argc, char** argv) {
    ROOT = powq(3, (Q - 1) >> TWO_ADICITY);
    if (const char* ri = getenv("FP_RATE_INV")) { g_rate_inv = atoi(ri); if (g_rate_inv != 2 && g_rate_inv != 4 && g_rate_inv != 8 && g_rate_inv != 16) { fprintf(stderr, "FP_RATE_INV must be 2, 4, 8 or 16\n"); return 2; } }
    if (const char* pd = getenv("FP_PROX_DIV")) { g_prox_div = atoi(pd); if (g_prox_div != 2 && g_prox_div != 3) { fprintf(stderr, "FP_PROX_DIV must be 2 or 3\n"); return 2; } }
    string mode = argc > 1 ? argv[1] : "";
    try {
        if (mode == "selftest") {
            Rng rng(1); int bad = 0;
            auto slow = [](u128 a, u128 b) { u128 r = 0; while (b) { if (b & 1) r = addq(r, a); a = addq(a, a); b >>= 1; } return r; };
            for (int i = 0; i < 200000; i++) { u128 a = rng.base(), b = rng.base(); if (i < 4) { a = Q - 1 - (i & 1); b = Q - 1 - (i >> 1); } if (mulq(a, b) != slow(a, b)) bad++; }
            F x = rng.f(), y = rng.f(), z = rng.f();
            if (fmul(fmul(x, y), z) != fmul(x, fmul(y, z)) || fmul(x, finv(x)) != FONE || fmul(FT, FT) != fint(3)) bad++;
            if (powq(ROOT, 1 << 23) != Q - 1) bad++;
            printf("selftest: %s\n", bad ? "FAILED" : "ok"); return bad ? 1 : 0;
        }
        if (mode == "prove") {
            int N = atoi(argv[2]), tau = atoi(argv[3]), C1 = atoi(argv[4]), C2 = atoi(argv[5]), qbits = atoi(argv[6]); u64 seed = strtoull(argv[7], 0, 10);
            string prefix = argc > 8 ? argv[8] : ""; if (prefix == "-") prefix = "";
            g_store = argc > 9 && string(argv[9]) == "store";
            Params par(N, tau, C1, C2, qbits); Instance in; Witness w; Timer T;
            gen_instance(N, tau, seed, in, w); double tgen = T.lap();
            Rng rng(seed * 7919 + 13);
            Proof pf = prove(par, in, w, rng); double tprove = T.lap();
            vector<u8> blob = serialize(par, pf);
            string why; bool ok = try_verify(par, in, deserialize(par, blob), &why); double tver = T.lap();
            struct rusage ru; getrusage(RUSAGE_SELF, &ru);
            printf("N=%d tau=%d C1=%d C2=%d  big: R=%d k=%d n=%d nq=%d  small: R=%d k=%d n=%d nq=%d\n", N, tau, C1, C2, par.big.R, par.big.k, par.big.n, par.big.nq, par.sm.R, par.sm.k, par.sm.n, par.sm.nq);
            printf("instance generation %.2fs\nPROVE %.3fs  (%.3f ms per ballot)%s\n", tgen, tprove, 1000 * tprove / tau, g_store ? "  [encoded matrix kept in memory]" : "  [streaming: two encoding passes]");
            for (auto& [k, v] : g_time) printf("   %-44s %8.3fs\n", k.c_str(), v);
            printf("VERIFY %.3fs  (%.3f ms per ballot)  -> %s\n", tver, 1000 * tver / tau, ok ? "accepted" : ("REJECTED: " + why).c_str());
            printf("proof %zu bytes (%.1f bytes per ballot); peak memory %.0f MB\n", blob.size(), (double)blob.size() / tau, RSS_TO_MB(ru.ru_maxrss));
            if (!ok) return 1;
            // negative checks: a tampered statement and three tampered proofs must be rejected
            Instance bad = in; bad.cout[5] = addq(bad.cout[5], 1);
            int rej = !try_verify(par, bad, pf);
            Rng tr(seed + 99);
            for (int t = 0; t < 3; t++) { vector<u8> b2 = blob; size_t p = tr.below(b2.size()); b2[p] ^= 1; bool acc; try { acc = try_verify(par, in, deserialize(par, b2)); } catch (Reject&) { acc = false; } rej += !acc; }
            printf("negative checks rejected: %d/4\n", rej);
            if (!prefix.empty()) { write_file(prefix + ".inst", ser_instance(in)); write_file(prefix + ".proof", blob); }
            return rej == 4 ? 0 : 1;
        }
        if (mode == "checkC") {                                    // specialised vs generic shortness sumcheck: identical messages
            int bad = 0, runs = 0;
            for (auto [N, tau] : vector<pair<int, int>>{{2, 2}, {4, 2}, {2, 16}, {8, 16}, {16, 64}, {64, 32}, {32, 512}, {256, 64}}) {
                Params par(N, tau, min(N * tau, 256), 256, 16); Instance in; Witness w; gen_instance(N, tau, 77 + N + tau, in, w);
                Rng rng(5 * N + tau); SCMask g(par.dC, rng); F rho = rng.f(), a0 = rng.f(), a1 = rng.f(), a2 = rng.f(); const F* aw[3] = {&a0, &a1, &a2};
                vector<F> tz(par.m), kC(3); for (auto& x : tz) x = rng.f(); for (auto& x : kC) x = rng.f();
                Challenger c1("t"), c2("t");
                SCOut s1 = sumcheck_C(c1, par, w, tz, kC, aw, g, rho);
                vector<vector<F>> tabs{eq_table(tz)};
                for (int k = 0; k < 3; k++) { vector<F> t((size_t)N * tau); for (size_t i = 0; i < t.size(); i++) t[i] = F{from_i8(w.W[k][i]), 0}; tabs.push_back(t); }
                vector<Term> terms; for (int k = 0; k < 3; k++) { terms.push_back({kC[k], {0, 1 + k, 1 + k, 1 + k}}); terms.push_back({fneg(kC[k]), {0, 1 + k}}); }
                SCOut s2 = sc_prove(c2, "C", tabs, {nullptr, aw[0], aw[1], aw[2]}, terms, FZERO, par.m, 4, 7, g, rho);
                bool same = s1.msgs == s2.msgs && s1.point == s2.point && s1.finals == s2.finals && s1.claim == s2.claim;
                printf("N=%4d tau=%4d (m=%2d): %s\n", N, tau, par.m, same ? "identical" : "DIFFERENT"); bad += !same; runs++;
            }
            printf("checkC: %d/%d identical\n", runs - bad, runs); return bad ? 1 : 0;
        }
        if (mode == "decprove") {                                  // decprove N tau base kdig C1 C2 qbits seed [prefix|-] [generic]
            int N = atoi(argv[2]), tau = atoi(argv[3]), base = atoi(argv[4]), kd = atoi(argv[5]), C1 = atoi(argv[6]), C2 = atoi(argv[7]), qbits = atoi(argv[8]);
            u64 seed = strtoull(argv[9], 0, 10); string prefix = argc > 10 ? argv[10] : ""; if (prefix == "-") prefix = "";
            bool generic = argc > 11 && string(argv[11]) == "generic";
            DecParams par(N, tau, base, kd, C1, C2, qbits); DecStmt st; vector<int8_t> s, e; vector<vector<u8>> D; Timer T;
            gen_dec(par, seed, st, s, e, D); double tgen = T.lap();
            Rng rng(seed * 7919 + 17);
            DecProof pf = dec_prove(par, st, s, e, D, rng, generic); double tprove = T.lap();
            vector<u8> blob = ser_dproof(pf);
            string why; bool ok = try_dverify(par, st, de_dproof(par, blob), &why); double tver = T.lap();
            long fs, os; dec_size_model(N, tau, base, kd, par.C1, par.C2, par.rate_inv, qbits, fs, os);
            struct rusage ru; getrusage(RUSAGE_SELF, &ru);
            printf("N=%d tau=%d base=%d kdig=%d C1=%d C2=%d  big: R=%d k=%d n=%d nq=%d  small: R=%d k=%d n=%d nq=%d\n", N, tau, base, kd, par.C1, par.C2,
                   par.big.R, par.big.k, par.big.n, par.big.nq, par.sm.R, par.sm.k, par.sm.n, par.sm.nq);
            printf("instance generation %.2fs\nPROVE %.3fs  (%.3f ms per ballot)%s\n", tgen, tprove, 1000 * tprove / tau, generic ? "  [generic sumcheck G]" : "");
            for (auto& [k, v] : g_time) printf("   %-44s %8.3fs\n", k.c_str(), v);
            printf("VERIFY %.3fs  (%.3f ms per ballot)  -> %s\n", tver, 1000 * tver / tau, ok ? "accepted" : ("REJECTED: " + why).c_str());
            printf("proof %zu bytes (%.1f bytes per ballot), size model %ld: %s; peak memory %.0f MB\n", blob.size(), (double)blob.size() / tau, fs + os,
                   (long)blob.size() == fs + os ? "exact" : "DIFFERENT", RSS_TO_MB(ru.ru_maxrss));
            if (!ok || (long)blob.size() != fs + os) return 1;
            DecStmt bad = st; bad.ts[3] = addq(bad.ts[3], 1);
            int rej = !try_dverify(par, bad, pf);
            Rng tr(seed + 99);
            for (int t = 0; t < 3; t++) { vector<u8> b2 = blob; size_t p = tr.below(b2.size()); b2[p] ^= 1; bool acc; try { acc = try_dverify(par, st, de_dproof(par, b2)); } catch (Reject&) { acc = false; } rej += !acc; }
            printf("negative checks rejected: %d/4\n", rej);
            if (!prefix.empty()) { write_file(prefix + ".stmt", ser_dstmt(st)); write_file(prefix + ".proof", blob); }
            return rej == 4 ? 0 : 1;
        }
        if (mode == "decverify") {                                 // decverify N tau base kdig C1 C2 qbits stmt proof
            int N = atoi(argv[2]), tau = atoi(argv[3]), base = atoi(argv[4]), kd = atoi(argv[5]), C1 = atoi(argv[6]), C2 = atoi(argv[7]), qbits = atoi(argv[8]);
            DecParams par(N, tau, base, kd, C1, C2, qbits); string why; bool ok;
            try { ok = try_dverify(par, de_dstmt(read_file(argv[9])), de_dproof(par, read_file(argv[10])), &why); } catch (Reject& e) { ok = false; why = e.what(); }
            printf("%s\n", ok ? "accepted" : ("rejected: " + why).c_str()); return ok ? 0 : 1;
        }
        if (mode == "checkG") {                                    // specialised vs generic digit sumcheck: identical messages
            int bad = 0, runs = 0;
            for (auto [N, tau, base, kd] : vector<array<int, 4>>{{2, 2, 2, 3}, {4, 2, 2, 8}, {8, 16, 2, 8}, {4, 64, 4, 3}, {16, 32, 4, 5}, {8, 8, 16, 2},
                                                                   {32, 64, 16, 3}, {64, 256, 2, 4}, {16, 1024, 4, 3}, {256, 64, 8, 2}}) {
                DecParams par(N, tau, base, kd, 0, 0, 16); DecStmt st; vector<int8_t> s, e; vector<vector<u8>> D;
                gen_dec(par, 41 + N + tau + base, st, s, e, D);
                Rng rng(3 * N + tau); SCMask g(par.dG, rng); F rho = rng.f();
                vector<F> ad(kd), tz(par.m), kG(kd); for (auto& x : ad) x = rng.f(); for (auto& x : tz) x = rng.f(); for (auto& x : kG) x = rng.f();
                Challenger c1("t"), c2("t");
                SCOut s1 = sumcheck_G(c1, par, D, tz, kG, ad, g, rho);
                vector<vector<F>> tabs{eq_table(tz)};
                for (int d = 0; d < kd; d++) { vector<F> t((size_t)N * tau); for (size_t i = 0; i < t.size(); i++) t[i] = fint(D[d][i]); tabs.push_back(t); }
                vector<const F*> tm{nullptr}; for (auto& a : ad) tm.push_back(&a);
                SCOut s2 = sc_prove(c2, "G", tabs, tm, g_terms(kG, base), FZERO, par.m, base + 1, 2 * base + 1, g, rho);
                bool same = s1.msgs == s2.msgs && s1.point == s2.point && s1.finals == s2.finals && s1.claim == s2.claim;
                printf("N=%4d tau=%4d base=%2d kdig=%d (m=%2d): %s\n", N, tau, base, kd, par.m, same ? "identical" : "DIFFERENT"); bad += !same; runs++;
            }
            printf("checkG: %d/%d identical\n", runs - bad, runs); return bad ? 1 : 0;
        }
        if (mode == "verify") {
            int N = atoi(argv[2]), tau = atoi(argv[3]), C1 = atoi(argv[4]), C2 = atoi(argv[5]), qbits = atoi(argv[6]);
            Params par(N, tau, C1, C2, qbits); Instance in = de_instance(read_file(argv[7]));
            if (in.N != N || in.tau != tau) throw runtime_error("instance does not match the parameters");
            string why; bool ok;
            try { ok = try_verify(par, in, deserialize(par, read_file(argv[8])), &why); } catch (Reject& e) { ok = false; why = e.what(); }
            printf("%s\n", ok ? "accepted" : ("rejected: " + why).c_str()); return ok ? 0 : 1;
        }
    } catch (exception& e) { fprintf(stderr, "error: %s\n", e.what()); return 2; }
    fprintf(stderr, "usage: mixnative selftest | checkC | checkG | prove N tau C1 C2 qbits seed [prefix] | verify N tau C1 C2 qbits inst proof\n"
                    "       | decprove N tau base kdig C1 C2 qbits seed [prefix] [generic] | decverify N tau base kdig C1 C2 qbits stmt proof   (C1, C2 = 0: defaults)\n");
    return 2;
}
