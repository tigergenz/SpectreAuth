--[[
  SPECTREAUTH All-in-One Client Bundle for Roblox Executors & Luau.
  Contains both pure-Lua Ed25519 verifier and SpectreAuth client SDK.
  
  Zero dependencies:
    - Auto-detects Executor HTTP (syn.request, http.request, fluxus.request, request, http_request)
    - Auto-detects Hardware ID (gethwid(), get_hwid(), ClientId, LocalPlayer.UserId)
    - Auto-wires Ed25519 verification when publicKey is passed
    - Compatible with Wave, Solara, Swift, Fluxus, Delta, Codex, Synapse, Studio, and Luau

  Usage in Executor:
    local SpectreAuth = loadstring(game:HttpGet("https://raw.githubusercontent.com/.../spectreauth_bundle.lua"))()
    local auth = SpectreAuth.new({
        baseUrl   = "https://auth.example.workers.dev",
        appId     = "YOUR_APP_ID",
        publicKey = "PROJECT_PUBLIC_KEY",
    })
    local ok, code, msg = auth:login("SPEC-XXXXX-XXXXX-XXXXX-XXXXX")
]]

local Ed25519 = (function()
    --[[
      Pure-Lua Ed25519 *verification* (RFC 8032) for Luau and Lua 5.1/LuaJIT. Verify only: no signing.

        local Ed25519 = require("ed25519")
        local auth = SpectreAuth.new({ ..., publicKey = PUB, verify = Ed25519.verify })

      Needs a 32-bit bit library (`bit32` on Luau/Lua 5.2, `bit` on LuaJIT). Numbers are plain doubles:
      field elements use 11 limbs of 24 bits so every intermediate stays below 2^53.
      SHA-512 constants are derived at first use (fractional parts of prime roots) instead of being
      hard-coded, and the module is checked against RFC 8032 and SHA-512 test vectors in test/lua.

      Cost: roughly 17k field multiplications per verification (tens of ms on LuaJIT, a few hundred on
      Luau). Not constant-time. That is fine here because every input is public.
    ]]

    local Ed25519 = {}

    local bitlib = bit32 or bit
    assert(bitlib, "ed25519: needs bit32 (Luau/5.2) or bit (LuaJIT)")
    local T32 = 4294967296
    local function u32(x) return x % T32 end
    local band, bor, bxor, rshift, lshift = bitlib.band, bitlib.bor, bitlib.bxor, bitlib.rshift, bitlib.lshift
    local floor = math.floor

    -- ============================================================ generic little-endian bignums (base 2^24)

    local B = 16777216

    local function bmul(a, b)
        local c = {}
        for i = 1, #a + #b do c[i] = 0 end
        for i = 1, #a do
            for j = 1, #b do c[i + j - 1] = c[i + j - 1] + a[i] * b[j] end
        end
        for i = 1, #c - 1 do
            local carry = floor(c[i] / B)
            c[i] = c[i] - carry * B
            c[i + 1] = c[i + 1] + carry
        end
        return c
    end

    local function bcmp(a, b)
        local n = math.max(#a, #b)
        for i = n, 1, -1 do
            local x, y = a[i] or 0, b[i] or 0
            if x ~= y then return x < y and -1 or 1 end
        end
        return 0
    end

    local function bitOf(x, i)
        return floor((x[floor(i / 24) + 1] or 0) / 2 ^ (i % 24)) % 2
    end

    -- Integer root of N (limb array) by building the answer bit by bit; `power` is 2 or 3.
    local function iroot(N, power, topBit)
        local x = {}
        for i = 1, floor(topBit / 24) + 1 do x[i] = 0 end
        for bitIndex = topBit, 0, -1 do
            local limb, val = floor(bitIndex / 24) + 1, 2 ^ (bitIndex % 24)
            x[limb] = x[limb] + val
            local p = bmul(x, x)
            if power == 3 then p = bmul(p, x) end
            if bcmp(p, N) > 0 then x[limb] = x[limb] - val end
        end
        return x
    end

    -- ============================================================ SHA-512

    local K_HI, K_LO, H0_HI, H0_LO

    local function takeWord(x, shift)
        local hi, lo = 0, 0
        for i = 31, 0, -1 do lo = lo * 2 + bitOf(x, shift + i) end
        for i = 63, 32, -1 do hi = hi * 2 + bitOf(x, shift + i) end
        return hi, lo
    end

    local function initConstants()
        if K_HI then return end
        local primes, n = {}, 2
        while #primes < 80 do
            local isPrime = true
            for _, p in ipairs(primes) do
                if p * p > n then break end
                if n % p == 0 then isPrime = false break end
            end
            if isPrime then primes[#primes + 1] = n end
            n = n + 1
        end
        K_HI, K_LO, H0_HI, H0_LO = {}, {}, {}, {}
        for i = 1, 80 do
            -- floor(cbrt(p) * 2^64): integer cube root of p * 2^192
            local N = { 0, 0, 0, 0, 0, 0, 0, 0, primes[i] }
            K_HI[i], K_LO[i] = takeWord(iroot(N, 3, 71), 0)
        end
        for i = 1, 8 do
            -- floor(sqrt(p) * 2^64): integer sqrt of p * 2^144 gives sqrt(p) * 2^72, drop 8 bits
            local N = { 0, 0, 0, 0, 0, 0, primes[i] }
            H0_HI[i], H0_LO[i] = takeWord(iroot(N, 2, 75), 8)
        end
    end

    local function rotr(h, l, n)
        if n == 32 then return l, h end
        if n > 32 then h, l = l, h; n = n - 32 end
        local m = 32 - n
        return u32(bor(rshift(h, n), lshift(l, m))), u32(bor(rshift(l, n), lshift(h, m)))
    end

    local function shr(h, l, n)
        return rshift(h, n), u32(bor(rshift(l, n), lshift(h, 32 - n)))
    end

    local function xor3(a, b, c) return u32(bxor(bxor(a, b), c)) end

    local function add64(ah, al, bh, bl)
        local l = al + bl
        local h = ah + bh + (l >= T32 and 1 or 0)
        return h % T32, l % T32
    end

    local function sha512(bytes)
        initConstants()
        local len = #bytes
        local msg = {}
        for i = 1, len do msg[i] = bytes[i] end
        msg[#msg + 1] = 0x80
        while #msg % 128 ~= 112 do msg[#msg + 1] = 0 end
        for _ = 1, 12 do msg[#msg + 1] = 0 end
        local bits = len * 8
        msg[#msg + 1] = floor(bits / 16777216) % 256
        msg[#msg + 1] = floor(bits / 65536) % 256
        msg[#msg + 1] = floor(bits / 256) % 256
        msg[#msg + 1] = bits % 256

        local Hh, Hl = {}, {}
        for i = 1, 8 do Hh[i], Hl[i] = H0_HI[i], H0_LO[i] end

        for blk = 0, #msg / 128 - 1 do
            local Wh, Wl = {}, {}
            for t = 0, 15 do
                local o = blk * 128 + t * 8
                Wh[t + 1] = ((msg[o + 1] * 256 + msg[o + 2]) * 256 + msg[o + 3]) * 256 + msg[o + 4]
                Wl[t + 1] = ((msg[o + 5] * 256 + msg[o + 6]) * 256 + msg[o + 7]) * 256 + msg[o + 8]
            end
            for t = 17, 80 do
                local h2, l2 = Wh[t - 2], Wl[t - 2]
                local a1, b1 = rotr(h2, l2, 19); local a2, b2 = rotr(h2, l2, 61); local a3, b3 = shr(h2, l2, 6)
                local s1h, s1l = xor3(a1, a2, a3), xor3(b1, b2, b3)
                local h15, l15 = Wh[t - 15], Wl[t - 15]
                a1, b1 = rotr(h15, l15, 1); a2, b2 = rotr(h15, l15, 8); a3, b3 = shr(h15, l15, 7)
                local s0h, s0l = xor3(a1, a2, a3), xor3(b1, b2, b3)
                local h, l = add64(s1h, s1l, Wh[t - 7], Wl[t - 7])
                h, l = add64(h, l, s0h, s0l)
                Wh[t], Wl[t] = add64(h, l, Wh[t - 16], Wl[t - 16])
            end

            local ah, al, bh, bl, ch, cl, dh, dl = Hh[1], Hl[1], Hh[2], Hl[2], Hh[3], Hl[3], Hh[4], Hl[4]
            local eh, el, fh, fl, gh, gl, hh, hl = Hh[5], Hl[5], Hh[6], Hl[6], Hh[7], Hl[7], Hh[8], Hl[8]
            for t = 1, 80 do
                local r1, r2 = rotr(eh, el, 14); local r3, r4 = rotr(eh, el, 18); local r5, r6 = rotr(eh, el, 41)
                local S1h, S1l = xor3(r1, r3, r5), xor3(r2, r4, r6)
                local chh = u32(bxor(band(eh, fh), band(u32(bxor(eh, 0xFFFFFFFF)), gh)))
                local chl = u32(bxor(band(el, fl), band(u32(bxor(el, 0xFFFFFFFF)), gl)))
                local t1h, t1l = add64(hh, hl, S1h, S1l)
                t1h, t1l = add64(t1h, t1l, chh, chl)
                t1h, t1l = add64(t1h, t1l, K_HI[t], K_LO[t])
                t1h, t1l = add64(t1h, t1l, Wh[t], Wl[t])

                r1, r2 = rotr(ah, al, 28); r3, r4 = rotr(ah, al, 34); r5, r6 = rotr(ah, al, 39)
                local S0h, S0l = xor3(r1, r3, r5), xor3(r2, r4, r6)
                local mjh = xor3(band(ah, bh), band(ah, ch), band(bh, ch))
                local mjl = xor3(band(al, bl), band(al, cl), band(bl, cl))
                local t2h, t2l = add64(S0h, S0l, mjh, mjl)

                hh, hl, gh, gl, fh, fl = gh, gl, fh, fl, eh, el
                eh, el = add64(dh, dl, t1h, t1l)
                dh, dl, ch, cl, bh, bl = ch, cl, bh, bl, ah, al
                ah, al = add64(t1h, t1l, t2h, t2l)
            end
            local vh = { ah, bh, ch, dh, eh, fh, gh, hh }
            local vl = { al, bl, cl, dl, el, fl, gl, hl }
            for i = 1, 8 do Hh[i], Hl[i] = add64(Hh[i], Hl[i], vh[i], vl[i]) end
        end

        local out = {}
        for i = 1, 8 do
            for _, w in ipairs({ Hh[i], Hl[i] }) do
                out[#out + 1] = floor(w / 16777216) % 256
                out[#out + 1] = floor(w / 65536) % 256
                out[#out + 1] = floor(w / 256) % 256
                out[#out + 1] = w % 256
            end
        end
        return out
    end

    -- ============================================================ field arithmetic mod p = 2^255 - 19

    local P2 -- limbs of 2p

    local function normalize(c, len)
        for i = 1, len - 1 do
            local carry = floor(c[i] / B)
            c[i] = c[i] - carry * B
            c[i + 1] = c[i + 1] + carry
        end
    end

    -- value = lo + 2^255 * hi  ==  lo + 19 * hi   (mod p)
    local function fold(c, len)
        local out = {}
        for i = 1, 10 do out[i] = c[i] end
        out[11] = (c[11] or 0) % 32768
        local j = 0
        while 11 + j <= len do
            local h = floor(c[11 + j] / 32768) + ((c[12 + j] or 0) % 32768) * 512
            out[1 + j] = (out[1 + j] or 0) + 19 * h
            j = j + 1
        end
        return out
    end

    local function reduce(c, len)
        normalize(c, len)
        local r = fold(c, len)
        local rl = math.max(#r, 12)
        for i = #r + 1, rl do r[i] = 0 end
        normalize(r, rl)
        r = fold(r, rl)
        rl = math.max(#r, 12)
        for i = #r + 1, rl do r[i] = 0 end
        normalize(r, rl)
        for i = 12, rl do assert(r[i] == 0, "ed25519: field reduction overflow") end
        for i = 12, rl do r[i] = nil end
        return r
    end

    local function fe_int(n)
        return { n, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 }
    end

    local function fe_add(a, b)
        local c = {}
        for i = 1, 11 do c[i] = a[i] + b[i] end
        return reduce(c, 11)
    end

    local function fe_sub(a, b)
        local c = {}
        for i = 1, 11 do c[i] = a[i] + P2[i] - b[i] end
        return reduce(c, 11)
    end

    local function fe_mul(a, b)
        local c = {}
        for i = 1, 23 do c[i] = 0 end
        for i = 1, 11 do
            local ai = a[i]
            for j = 1, 11 do c[i + j - 1] = c[i + j - 1] + ai * b[j] end
        end
        return reduce(c, 23)
    end

    local function fe_freeze(a)
        local r = {}
        for i = 1, 11 do r[i] = a[i] end
        for _ = 1, 2 do
            local t = {}
            for i = 1, 11 do t[i] = r[i] end
            t[1] = t[1] + 19
            normalize(t, 11)
            if t[11] >= 32768 then
                t[11] = t[11] - 32768
                r = t
            end
        end
        return r
    end

    local function fe_eq(a, b)
        local x, y = fe_freeze(a), fe_freeze(b)
        for i = 1, 11 do if x[i] ~= y[i] then return false end end
        return true
    end

    local function fe_pow(a, nOnes, tail)
        local r = a
        for _ = 2, nOnes do r = fe_mul(fe_mul(r, r), a) end
        for i = 1, #tail do
            r = fe_mul(r, r)
            if tail:sub(i, i) == "1" then r = fe_mul(r, a) end
        end
        return r
    end

    local function fe_inv(a) return fe_pow(a, 250, "01011") end -- a^(p-2)

    local function fe_fromBytes(bytes)
        local r = {}
        for i = 1, 11 do
            local o = (i - 1) * 3
            r[i] = (bytes[o + 1] or 0) + (bytes[o + 2] or 0) * 256 + (bytes[o + 3] or 0) * 65536
        end
        return r
    end

    local function fe_toBytes(a)
        local f = fe_freeze(a)
        local out = {}
        for i = 1, 11 do
            out[#out + 1] = f[i] % 256
            out[#out + 1] = floor(f[i] / 256) % 256
            out[#out + 1] = floor(f[i] / 65536) % 256
        end
        for i = 33, #out do out[i] = nil end
        return out
    end

    -- ============================================================ curve: -x^2 + y^2 = 1 + d x^2 y^2

    local D, D2, SQRTM1, BASE, IDENTITY

    local function initCurve()
        if D then return end
        -- p = 2^255 - 19 as limbs, then 2p
        local p = {}
        for i = 1, 10 do p[i] = 0xFFFFFF end
        p[11] = 0x7FFF
        p[1] = 0xFFFFED
        P2 = {}
        local carry = 0
        for i = 1, 11 do
            local v = p[i] * 2 + carry
            carry = floor(v / B)
            P2[i] = v - carry * B
        end
        P2[12] = carry
        for i = 12, #P2 do if P2[i] == 0 then P2[i] = nil end end -- 2p < 2^256, always 11 limbs

        local neg = function(n) return fe_sub(fe_int(0), fe_int(n)) end
        D = fe_mul(neg(121665), fe_inv(fe_int(121666)))
        D2 = fe_add(D, D)
        SQRTM1 = fe_pow(fe_int(2), 250, "011") -- 2^((p-1)/4)
        IDENTITY = { fe_int(0), fe_int(1), fe_int(1), fe_int(0) }
    end

    local function pt_add(P, Q)
        local X1, Y1, Z1, T1 = P[1], P[2], P[3], P[4]
        local X2, Y2, Z2, T2 = Q[1], Q[2], Q[3], Q[4]
        local A = fe_mul(fe_sub(Y1, X1), fe_sub(Y2, X2))
        local Bv = fe_mul(fe_add(Y1, X1), fe_add(Y2, X2))
        local C = fe_mul(fe_mul(T1, D2), T2)
        local Dv = fe_mul(Z1, Z2)
        Dv = fe_add(Dv, Dv)
        local E, F, G, H = fe_sub(Bv, A), fe_sub(Dv, C), fe_add(Dv, C), fe_add(Bv, A)
        return { fe_mul(E, F), fe_mul(G, H), fe_mul(F, G), fe_mul(E, H) }
    end

    local function pt_mul(P, scalar) -- scalar: 32 little-endian bytes
        local R = IDENTITY
        for bitIndex = 255, 0, -1 do
            R = pt_add(R, R)
            if band(rshift(scalar[floor(bitIndex / 8) + 1], bitIndex % 8), 1) == 1 then R = pt_add(R, P) end
        end
        return R
    end

    local function pt_eq(P, Q)
        return fe_eq(fe_mul(P[1], Q[3]), fe_mul(Q[1], P[3])) and fe_eq(fe_mul(P[2], Q[3]), fe_mul(Q[2], P[3]))
    end

    -- Returns a point, or nil if the 32 bytes are not a valid canonical encoding.
    local function pt_decode(bytes)
        if #bytes ~= 32 then return nil end
        local sign = floor(bytes[32] / 128)
        local yb = {}
        for i = 1, 32 do yb[i] = bytes[i] end
        yb[32] = yb[32] % 128
        local y = fe_fromBytes(yb)
        local canon = fe_toBytes(y)
        for i = 1, 32 do if canon[i] ~= yb[i] then return nil end end -- y >= p
        local one = fe_int(1)
        local y2 = fe_mul(y, y)
        local u = fe_sub(y2, one)
        local v = fe_add(fe_mul(D, y2), one)
        local v3 = fe_mul(fe_mul(v, v), v)
        local v7 = fe_mul(fe_mul(v3, v3), v)
        local x = fe_mul(fe_mul(u, v3), fe_pow(fe_mul(u, v7), 250, "01")) -- (u v^7)^((p-5)/8)
        local vx2 = fe_mul(v, fe_mul(x, x))
        if not fe_eq(vx2, u) then
            if fe_eq(vx2, fe_sub(fe_int(0), u)) then x = fe_mul(x, SQRTM1) else return nil end
        end
        local xb = fe_toBytes(x)
        local isZero = true
        for i = 1, 32 do if xb[i] ~= 0 then isZero = false break end end
        if isZero and sign == 1 then return nil end
        if xb[1] % 2 ~= sign then x = fe_sub(fe_int(0), x) end
        return { x, y, fe_int(1), fe_mul(x, y) }
    end

    local function initBase()
        initCurve()
        if BASE then return end
        -- B.y = 4/5, B.x even
        local y = fe_mul(fe_int(4), fe_inv(fe_int(5)))
        local enc = fe_toBytes(y)
        BASE = pt_decode(enc)
        assert(BASE, "ed25519: base point decode failed")
    end

    -- ============================================================ scalars mod L

    local L_BYTES = {
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
    }

    local function bytesLess(a, b) -- 32-byte little-endian compare: a < b
        for i = 32, 1, -1 do
            if a[i] ~= b[i] then return a[i] < b[i] end
        end
        return false
    end

    local function modL(bytes64)
        local Ll = fe_fromBytes(L_BYTES)
        local r = {}
        for i = 1, 11 do r[i] = 0 end
        for bitIndex = 511, 0, -1 do
            local bit = band(rshift(bytes64[floor(bitIndex / 8) + 1], bitIndex % 8), 1)
            local carry = bit
            for i = 1, 11 do
                local v = r[i] * 2 + carry
                carry = floor(v / B)
                r[i] = v - carry * B
            end
            if bcmp(r, Ll) >= 0 then
                local borrow = 0
                for i = 1, 11 do
                    local v = r[i] - Ll[i] - borrow
                    if v < 0 then v = v + B; borrow = 1 else borrow = 0 end
                    r[i] = v
                end
            end
        end
        local out = {}
        for i = 1, 11 do
            out[#out + 1] = r[i] % 256
            out[#out + 1] = floor(r[i] / 256) % 256
            out[#out + 1] = floor(r[i] / 65536) % 256
        end
        for i = 33, #out do out[i] = nil end
        return out
    end

    -- ============================================================ public API

    local function toBytes(s)
        local t = {}
        for i = 1, #s do t[i] = s:byte(i) end
        return t
    end

    local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
    local B64_INDEX = {}
    for i = 1, #B64 do B64_INDEX[B64:byte(i)] = i - 1 end

    local function b64uDecode(s)
        local out, acc, bits = {}, 0, 0
        for i = 1, #s do
            local v = B64_INDEX[s:byte(i)]
            if not v then return nil end
            acc = acc * 64 + v
            bits = bits + 6
            if bits >= 8 then
                bits = bits - 8
                out[#out + 1] = floor(acc / 2 ^ bits) % 256
                acc = acc % 2 ^ bits
            end
        end
        return out
    end

    --- Verify an Ed25519 signature. All arguments are byte tables; message may also be a string.
    function Ed25519.verifyBytes(message, sig, pub)
        if type(message) == "string" then message = toBytes(message) end
        if #sig ~= 64 or #pub ~= 32 then return false end
        initBase()
        local Rb, Sb = {}, {}
        for i = 1, 32 do Rb[i] = sig[i]; Sb[i] = sig[32 + i] end
        if not bytesLess(Sb, L_BYTES) then return false end -- reject malleable S
        local A = pt_decode(pub)
        local R = pt_decode(Rb)
        if not A or not R then return false end

        local hashInput = {}
        for i = 1, 32 do hashInput[#hashInput + 1] = Rb[i] end
        for i = 1, 32 do hashInput[#hashInput + 1] = pub[i] end
        for i = 1, #message do hashInput[#hashInput + 1] = message[i] end
        local k = modL(sha512(hashInput))

        local lhs = pt_mul(BASE, Sb)
        local rhs = pt_add(R, pt_mul(A, k))
        return pt_eq(lhs, rhs)
    end

    --- Adapter matching SpectreAuth's `opts.verify(message, sigB64u, pubKeyB64u)`.
    --- Any malformed input or internal error yields false (never true by accident).
    function Ed25519.verify(message, sigB64u, pubB64u)
        local ok, res = pcall(function()
            local sig, pub = b64uDecode(sigB64u or ""), b64uDecode(pubB64u or "")
            if not sig or not pub then return false end
            return Ed25519.verifyBytes(message, sig, pub)
        end)
        return ok and res == true
    end

    Ed25519._internal = { sha512 = sha512, b64uDecode = b64uDecode, toBytes = toBytes }

    return Ed25519

end)()

local SpectreAuth = (function()
    --[[
      SPECTREAUTH client SDK for Lua 5.1+ / LuaJIT / Luau.

        local SpectreAuth = require("spectreauth")
        local auth = SpectreAuth.new({
            baseUrl = "https://auth.example.workers.dev",
            appId   = "YOUR_APP_ID",
            -- Optional but recommended: pin the project's Ed25519 public key and supply a verifier.
            -- publicKey = "…", verify = function(message, sigB64u, pubB64u) … end,
        })
        local ok, err = auth:login(key)

      Host integration points (all optional on Roblox, where sensible defaults exist):
        opts.http(method, url, headers, body) -> status:number, body:string, headers:table|nil
        opts.hwid                      string or function() -> string
        opts.json = { encode = fn, decode = fn }
        opts.verify(message, sigB64u, pubKeyB64u) -> boolean   (Ed25519 verify)

      Security notes:
        * Every response must echo the request nonce and carry a recent `ts`; mismatches are rejected,
          which blocks replayed "ok" responses.
        * If `publicKey` is set, responses that fail Ed25519 verification are rejected. Configuring a
          publicKey without a `verify` function is an error (fails closed rather than silently skipping).
        * Client-side checks can always be patched out by whoever controls the runtime. Treat this SDK as
          the transport; enforce what matters on a server you control.
    ]]

    local SpectreAuth = {}
    SpectreAuth.__index = SpectreAuth

    local MAX_CLOCK_SKEW = 120

    -- ---------------------------------------------------------------- environment adapters

    local HttpService do
        local ok, svc = pcall(function() return game:GetService("HttpService") end)
        if ok then HttpService = svc end
    end

    local function getGlobal(name)
        if SpectreAuth._executorEnv and SpectreAuth._executorEnv[name] ~= nil then
            return SpectreAuth._executorEnv[name]
        end
        if type(getgenv) == "function" then
            local ok, val = pcall(function() return getgenv()[name] end)
            if ok and val ~= nil then return val end
        end
        local okG, valG = pcall(function() return rawget(_G, name) end)
        if okG and valG ~= nil then return valG end
        local okR, valR = pcall(function()
            if name == "request" then return request
            elseif name == "http_request" then return http_request
            elseif name == "syn" then return syn
            elseif name == "http" then return http
            elseif name == "fluxus" then return fluxus
            elseif name == "gethwid" then return gethwid
            elseif name == "get_hwid" then return get_hwid
            end
        end)
        if okR and valR ~= nil then return valR end
        return nil
    end

    local function getExecutorRequest()
        local synObj = getGlobal("syn")
        if type(synObj) == "table" and type(synObj.request) == "function" then return synObj.request end
        local httpObj = getGlobal("http")
        if type(httpObj) == "table" and type(httpObj.request) == "function" then return httpObj.request end
        local fluxusObj = getGlobal("fluxus")
        if type(fluxusObj) == "table" and type(fluxusObj.request) == "function" then return fluxusObj.request end

        local r = getGlobal("request")
        if type(r) == "function" then return r end
        local hr = getGlobal("http_request")
        if type(hr) == "function" then return hr end
        return nil
    end

    local function defaultHttp(method, url, headers, body)
        -- 1. Exploit / Script Executor environment (Wave, Solara, Swift, Fluxus, Synapse, etc.)
        local execReq = getExecutorRequest()
        if execReq then
            local res = execReq({
                Url = url,
                Method = method,
                Headers = headers,
                Body = body,
            })
            if type(res) == "table" then
                local statusCode = res.StatusCode or res.status_code or res.Status or 200
                local respBody = res.Body or res.body or ""
                local respHeaders = res.Headers or res.headers
                return statusCode, respBody, respHeaders
            end
        end

        -- 2. Roblox Studio / Server environment (ServerScriptService)
        if HttpService then
            local isClient = false
            pcall(function()
                local runService = game:GetService("RunService")
                if runService and runService:IsClient() and not runService:IsStudio() then
                    isClient = true
                end
            end)
            if not isClient then
                local okReq, res = pcall(function()
                    return HttpService:RequestAsync({ Url = url, Method = method, Headers = headers, Body = body })
                end)
                if okReq and res then
                    return res.StatusCode, res.Body, res.Headers
                end
            end
        end

        -- 3. LuaSocket (Lua 5.1 / LuaJIT standalone)
        local okSsl, https = pcall(require, "ssl.https")
        local okLtn, ltn12 = pcall(require, "ltn12")
        if okSsl and okLtn then
            local chunks = {}
            local _, status, respHeaders = https.request({
                url = url, method = method, headers = headers,
                source = body and ltn12.source.string(body) or nil,
                sink = ltn12.sink.table(chunks),
            })
            return status, table.concat(chunks), respHeaders
        end
        error("SpectreAuth: no HTTP backend found; pass opts.http")
    end

    -- Minimal JSON codec (used only when the host doesn't provide one).
    local function jsonEncode(v)
        local t = type(v)
        if t == "string" then
            return '"' .. v:gsub('[%c"\\]', function(c)
                return string.format("\\u%04x", c:byte())
            end) .. '"'
        elseif t == "number" or t == "boolean" then
            return tostring(v)
        elseif t == "table" then
            local parts = {}
            for k, val in pairs(v) do
                parts[#parts + 1] = jsonEncode(tostring(k)) .. ":" .. jsonEncode(val)
            end
            return "{" .. table.concat(parts, ",") .. "}"
        end
        return "null"
    end

    local function jsonDecode(s)
        local pos = 1
        local function ws() pos = s:find("%S", pos) or #s + 1 end
        local value
        local function str()
            local out, i = {}, pos + 1
            while true do
                local c = s:sub(i, i)
                if c == "" then error("unterminated string") end
                if c == '"' then pos = i + 1; return table.concat(out) end
                if c == "\\" then
                    local n = s:sub(i + 1, i + 1)
                    if n == "u" then
                        local code = tonumber(s:sub(i + 2, i + 5), 16)
                        out[#out + 1] = code < 128 and string.char(code) or "?"
                        i = i + 6
                    else
                        out[#out + 1] = ({ n = "\n", t = "\t", r = "\r", b = "\b", f = "\f" })[n] or n
                        i = i + 2
                    end
                else
                    out[#out + 1] = c; i = i + 1
                end
            end
        end
        function value()
            ws()
            local c = s:sub(pos, pos)
            if c == "{" then
                local obj = {}; pos = pos + 1; ws()
                if s:sub(pos, pos) == "}" then pos = pos + 1; return obj end
                while true do
                    ws(); local k = str(); ws()
                    assert(s:sub(pos, pos) == ":", "expected ':'"); pos = pos + 1
                    obj[k] = value(); ws()
                    local d = s:sub(pos, pos); pos = pos + 1
                    if d == "}" then return obj end
                    assert(d == ",", "expected ','")
                end
            elseif c == "[" then
                local arr = {}; pos = pos + 1; ws()
                if s:sub(pos, pos) == "]" then pos = pos + 1; return arr end
                while true do
                    arr[#arr + 1] = value(); ws()
                    local d = s:sub(pos, pos); pos = pos + 1
                    if d == "]" then return arr end
                    assert(d == ",", "expected ','")
                end
            elseif c == '"' then return str()
            elseif s:sub(pos, pos + 3) == "true" then pos = pos + 4; return true
            elseif s:sub(pos, pos + 4) == "false" then pos = pos + 5; return false
            elseif s:sub(pos, pos + 3) == "null" then pos = pos + 4; return nil
            else
                local num = s:match("^-?%d+%.?%d*[eE]?[+-]?%d*", pos)
                assert(num and #num > 0, "bad json at " .. pos)
                pos = pos + #num
                return tonumber(num)
            end
        end
        return value()
    end

    local function newNonce()
        if HttpService then
            return (HttpService:GenerateGUID(false):gsub("[^%w]", ""))
        end
        local alphabet = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
        local out = {}
        for i = 1, 24 do
            local r = math.random(1, #alphabet)
            out[i] = alphabet:sub(r, r)
        end
        return table.concat(out)
    end

    local function now()
        return (SpectreAuth._clock or os.time)() -- _clock: test hook
    end

    -- ---------------------------------------------------------------- client

    function SpectreAuth.new(opts)
        assert(type(opts) == "table", "opts required")
        assert(type(opts.baseUrl) == "string" and opts.baseUrl:match("^https://"), "baseUrl must be https://")
        assert(type(opts.appId) == "string", "appId required")
        if opts.publicKey then
            assert(type(opts.verify) == "function", "publicKey set but no opts.verify supplied (refusing to skip verification)")
        end
        local self = setmetatable({}, SpectreAuth)
        self.baseUrl = opts.baseUrl:gsub("/+$", "")
        self.appId = opts.appId
        self.publicKey = opts.publicKey
        self.verify = opts.verify
        self.http = opts.http or defaultHttp
        self.json = opts.json or (HttpService and {
            encode = function(v) return HttpService:JSONEncode(v) end,
            decode = function(s) return HttpService:JSONDecode(s) end,
        }) or { encode = jsonEncode, decode = jsonDecode }
        self._hwid = opts.hwid
        self._nonceFn = opts.nonce -- test hook; production code should leave this nil
        self.access, self.refresh_token, self.accessExpiresAt, self.user = nil, nil, 0, nil
        return self
    end

    function SpectreAuth:_hwidValue()
        local h = self._hwid
        if type(h) == "function" then h = h() end
        if not h then
            -- 1. Try executor HWID functions
            local fn = getGlobal("gethwid") or getGlobal("get_hwid")
            if type(fn) == "function" then
                local ok, val = pcall(fn)
                if ok and val and #tostring(val) >= 8 then h = tostring(val) end
            end
        end

        if not h and type(game) ~= "nil" then
            -- 2. Try RbxAnalyticsService:GetClientId()
            pcall(function()
                h = game:GetService("RbxAnalyticsService"):GetClientId()
            end)

            -- 3. Fallback to LocalPlayer identifier if on client
            if not h or #tostring(h) < 8 then
                pcall(function()
                    local player = game:GetService("Players").LocalPlayer
                    if player and player.UserId and player.UserId > 0 then
                        h = "ROBLOX-UID-" .. tostring(player.UserId)
                    end
                end)
            end
        end
        assert(h and #tostring(h) >= 8, "SpectreAuth: provide opts.hwid (8+ printable characters)")
        return tostring(h)
    end

    -- Returns decoded table on authentic response, or nil, errorCode, message.
    function SpectreAuth:_call(path, payload, bearer)
        payload.app_id = self.appId
        payload.hwid = self:_hwidValue()
        local nonce = (self._nonceFn or newNonce)()
        payload.nonce = nonce

        local headers = { ["Content-Type"] = "application/json" }
        if bearer then headers["Authorization"] = "Bearer " .. bearer end
        local ok, status, body, respHeaders = pcall(self.http, "POST", self.baseUrl .. path, headers, self.json.encode(payload))
        if not ok then return nil, "network", tostring(status) end

        local decOk, data = pcall(self.json.decode, body)
        if not decOk or type(data) ~= "table" then return nil, "bad_response", "unparseable response (HTTP " .. tostring(status) .. ")" end

        -- Authenticity: nonce echo + freshness (+ signature when pinned).
        if data.nonce ~= nonce then
            -- Pre-project errors (rate limit, bad app id) are unsigned and carry no nonce.
            if data.ok == false and data.error then return nil, data.error, data.message end
            return nil, "nonce_mismatch", "response did not match request"
        end
        if type(data.ts) ~= "number" or math.abs(now() - data.ts) > MAX_CLOCK_SKEW then
            return nil, "stale_response", "response timestamp out of range (check system clock)"
        end
        if self.publicKey then
            local sig
            if respHeaders then
                for k, v in pairs(respHeaders) do
                    if tostring(k):lower() == "x-spectre-sig" then sig = v end
                end
            end
            if not sig or not self.verify(body, sig, self.publicKey) then
                return nil, "bad_signature", "response signature invalid"
            end
        end
        if not data.ok then return nil, data.error, data.message end
        return data
    end

    function SpectreAuth:_store(data)
        self.access = data.access_token or self.access
        self.refresh_token = data.refresh_token or self.refresh_token
        self.accessExpiresAt = now() + (data.expires_in or 0)
        self.user = data.user or self.user
    end

    --- Exchange a license key for a session. Returns true, or false + errorCode + message.
    function SpectreAuth:login(key)
        local data, code, msg = self:_call("/v1/auth/login", { key = key })
        if not data then return false, code, msg end
        self:_store(data)
        return true
    end

    function SpectreAuth:refreshSession()
        if not self.refresh_token then return false, "no_session", "not logged in" end
        local data, code, msg = self:_call("/v1/auth/refresh", { refresh_token = self.refresh_token })
        if not data then
            if code == "invalid_token" or code == "session_revoked" or code == "token_expired" then self:_clear() end
            return false, code, msg
        end
        self:_store(data)
        return true
    end

    --- Check the session is still valid, transparently refreshing a near-expiry access token.
    function SpectreAuth:validate()
        if not self.access then return false, "no_session", "not logged in" end
        if now() >= self.accessExpiresAt - 10 then
            local ok, code, msg = self:refreshSession()
            if not ok then return false, code, msg end
        end
        local data, code, msg = self:_call("/v1/auth/validate", {}, self.access)
        if not data then
            if code == "token_expired" then
                local ok = self:refreshSession()
                if ok then return self:validate() end
            end
            return false, code, msg
        end
        self.user = data.user or self.user
        return true
    end

    function SpectreAuth:logout()
        if self.access then self:_call("/v1/auth/logout", {}, self.access) end
        self:_clear()
    end

    function SpectreAuth:_clear()
        self.access, self.refresh_token, self.accessExpiresAt, self.user = nil, nil, 0, nil
    end

    --- Roblox/Luau helper: validate every `interval` seconds; calls onFail(code, msg) and stops on failure.
    function SpectreAuth:startHeartbeat(interval, onFail)
        local taskLib = (type(task) == "table" and task) or rawget(_G, "task")
        assert(taskLib, "startHeartbeat needs the Luau `task` library; call :validate() on your own timer instead")
        self._beating = true
        taskLib.spawn(function()
            while self._beating do
                taskLib.wait(interval)
                local ok, code, msg = self:validate()
                if not ok then
                    self._beating = false
                    if onFail then onFail(code, msg) else error("SpectreAuth: session invalid: " .. tostring(code)) end
                end
            end
        end)
    end

    function SpectreAuth:stopHeartbeat() self._beating = false end

    SpectreAuth._internal = { jsonEncode = jsonEncode, jsonDecode = jsonDecode }
    return SpectreAuth

end)()

SpectreAuth.Ed25519 = Ed25519

-- Auto-wire Ed25519 verifier if publicKey is provided without explicit verify function
local originalNew = SpectreAuth.new
function SpectreAuth.new(opts)
    if type(opts) == "table" and opts.publicKey and not opts.verify then
        opts.verify = Ed25519.verify
    end
    return originalNew(opts)
end

return SpectreAuth
