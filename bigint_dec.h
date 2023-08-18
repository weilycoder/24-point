/*
https://github.com/Baobaobear/MiniBigInteger

MIT License

Copyright (c) 2021 Baobaobear

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

#include <algorithm>
#include <cstring>
#include <string>
#include <vector>
#define BIGINT_STD_MOVE std::move
#if defined(_WIN64) || defined(_M_X64)
#define BIGINT_X64 1
#else
#define BIGINT_X64 0
#endif
#if !defined(BIGINT_LARGE_BASE) && BIGINT_X64
#define BIGINT_LARGE_BASE 1
#endif

namespace NTT_NS {

const int32_t NTT_POW = 24;
const int32_t NTT_G = 3;
#if BIGINT_X64
typedef int64_t ntt_base_t;
const int32_t NTT_P1 = 469762049;
const int32_t NTT_P1_INV = 130489458;
const int32_t NTT_P2 = 167772161;
const int32_t NTT_P2_INV = 104391568;
#else
typedef int32_t ntt_base_t;
const int32_t NTT_P1 = 111149057;
const int32_t NTT_P1_INV = 34952517;
const int32_t NTT_P2 = 104857601;
const int32_t NTT_P2_INV = 74099389;
#endif

static std::vector<size_t> ntt_ra[NTT_POW];
static size_t *ntt_r;

uint32_t log2(uint32_t n) {
	uint32_t r = 0;
	if (n >= 0x10000) r += 16, n >>= 16;
	if (n >= 0x100) r += 8, n >>= 8;
	if (n >= 0x10) r += 4, n >>= 4;
	if (n >= 0x4) r += 2, n >>= 2;
	if (n >= 0x2) r += 1, n >>= 1;
	return r;
}

template <int32_t NTT_MOD> struct NTT {
	typedef typename std::vector<ntt_base_t> ntt_vector_t;
	ntt_vector_t ntt_a, ntt_b;
	std::vector<int64_t> ntt_c;
	std::vector<ntt_vector_t> ntt_wa[2][NTT_POW];

#if BIGINT_X64
	inline ntt_base_t mul_mod(int64_t a, int64_t b) { return a * b % NTT_MOD; }
#else
	inline ntt_base_t mul_mod(int32_t a, int32_t b) {
		int32_t c = (int32_t)((double)a * b / NTT_MOD);
		return a * b - c * NTT_MOD;
	}
#endif
	ntt_base_t pow_mod(int64_t a, int64_t b) {
		int64_t ans = 1;
		a %= NTT_MOD;
		while (b) {
			if (b & 1) ans = ans * a % NTT_MOD;
			b >>= 1;
			a = a * a % NTT_MOD;
		}
		return (ntt_base_t)ans;
	}
	void transform(ntt_base_t a[], size_t len, int on) {
		for (size_t i = 0; i < len; i++) {
			if (i < ntt_r[i]) std::swap(a[i], a[ntt_r[i]]);
		}
		uint32_t lg2 = log2(len);
		std::vector<ntt_vector_t> &ntt = ntt_wa[on][lg2];
		if (ntt.empty()) {
			ntt.reserve(lg2);
			ntt.push_back(ntt_vector_t());
			ntt_vector_t &wn = ntt[0];
			ntt_base_t root = pow_mod(NTT_G, (NTT_MOD - 1) / len);
			if (on == 0) root = pow_mod(root, NTT_MOD - 2);
			wn.push_back(1);
			for (size_t i = 0; i < len; ++i)
				wn.push_back(mul_mod(wn.back(), root));
			size_t h = len;
			for (uint32_t mul = 1, s = 2; mul < lg2; ++mul, s *= 2) {
				ntt.push_back(ntt_vector_t());
				ntt_vector_t &wns = ntt[mul];
				wns.reserve(h /= 2);
				for (uint32_t i = 0; i < h; ++i) {
					wns.push_back(wn[i * s]);
				}
			}
		}
		for (size_t h = 1, pos = lg2 - 1; h < len; h <<= 1, --pos) {
			ntt_base_t *ntt_w = &ntt[pos].front();
			for (size_t j = 0; j < len; j += h << 1) {
				size_t e = j + h;
				for (size_t k = j; k < e; k++) {
					ntt_base_t t = mul_mod(ntt_w[k - j], a[k + h]);
					a[k + h] = a[k] - t + NTT_MOD;
					a[k] += t;
				}
			}
		}
		for (size_t j = 0; j < len; ++j)
			a[j] %= NTT_MOD;
		if (on == 0) {
			ntt_base_t inv = pow_mod(len, NTT_MOD - 2);
			for (size_t i = 0; i < len; i++)
				a[i] = mul_mod(a[i], inv);
		}
	}
	void mul_conv(size_t n) {
		transform(&ntt_a.front(), n, 1);
		transform(&ntt_b.front(), n, 1);
		for (size_t i = 0; i < n; i++)
			ntt_a[i] = mul_mod(ntt_a[i], ntt_b[i]);
		transform(&ntt_a.front(), n, 0);
	}
	void sqr_conv(size_t n) {
		transform(&ntt_a.front(), n, 1);
		for (size_t i = 0; i < n; i++)
			ntt_a[i] = mul_mod(ntt_a[i], ntt_a[i]);
		transform(&ntt_a.front(), n, 0);
	}
};

static NTT<NTT_P1> ntt1;
static NTT<NTT_P2> ntt2;

void ntt_prepare(size_t size_a, size_t size_b, size_t &len, int flag = 1) {
	len = 1;
	size_t L1 = size_a, L2 = size_b;
	int32_t id = log2(uint32_t(L1 + L2));
	if (uint32_t(L1 + L2) > 1u << id) ++id;
	len = size_t(1) << id;
	ntt1.ntt_a.resize(len);
	if (flag & 1) ntt1.ntt_b.resize(len);
	if (flag & 2) ntt2.ntt_a = ntt1.ntt_a;
	if (flag & 4) ntt2.ntt_b = ntt1.ntt_b;
	if (ntt_ra[id].empty()) {
		std::vector<size_t> &r = ntt_ra[id];
		r.resize(len);
		for (size_t i = 0; i < len; i++)
			r[i] = (r[i >> 1] >> 1) | ((i & 1) * (len >> 1));
	}
	ntt_r = &ntt_ra[id].front();
}

static void double_mod_rev(size_t n) {
	ntt1.ntt_c.resize(n);
	for (size_t i = 0; i < n; i++) {
		int64_t t = (ntt1.ntt_a[i] - ntt2.ntt_a[i]) % NTT_P1 + NTT_P1;
		ntt1.ntt_c[i] = t * NTT_P2_INV % NTT_P1 * NTT_P2 + ntt2.ntt_a[i];
	}
}

void mul_conv() {
	size_t n = ntt1.ntt_a.size();
	ntt1.mul_conv(n);
	ntt2.mul_conv(n);
	double_mod_rev(n);
}

void sqr_conv() {
	size_t n = ntt1.ntt_a.size();
	ntt1.sqr_conv(n);
	ntt2.sqr_conv(n);
	double_mod_rev(n);
}
} // namespace NTT_NS

namespace BigIntDecNS {
#if BIGINT_LARGE_BASE
const int32_t COMPRESS_MOD = 100000000;
const uint32_t COMPRESS_DIGITS = 8;
const int32_t COMPRESS_HALF_MOD = 10000;
const uint32_t COMPRESS_HALF_DIGITS = 4;
#else
const int32_t COMPRESS_MOD = 10000;
const uint32_t COMPRESS_DIGITS = 4;
#endif

const uint32_t BIGINT_NTT_THRESHOLD = BIGINT_X64 ? 1700 : 1300;
const uint32_t BIGINT_MUL_THRESHOLD = 90;
const uint32_t BIGINT_DIV_THRESHOLD = 1500;
const uint32_t BIGINT_DIVIDEDIV_THRESHOLD = BIGINT_MUL_THRESHOLD * 3;
#if BIGINT_X64
const uint32_t NTT_MAX_SIZE = 1 << 24;
#else
const uint32_t NTT_MAX_SIZE = 1 << 21;
#endif

template <typename T> inline T high_digit(T digit) { return digit / (T)COMPRESS_MOD; }

template <typename T> inline uint32_t low_digit(T digit) { return (uint32_t)(digit % (T)COMPRESS_MOD); }

class BigIntDec {
protected:
	typedef uint32_t base_t;
#if BIGINT_LARGE_BASE
	typedef int64_t carry_t;
	typedef uint64_t ucarry_t;
#else
	typedef int32_t carry_t;
	typedef uint32_t ucarry_t;
#endif
	int sign;
	std::vector<base_t> v;
	typedef BigIntDec BigInt_t;
	template <typename _Tx, typename _Ty> static inline void carry(_Tx &add, _Ty &baseval, _Tx newval) {
		add += newval;
		baseval = low_digit(add);
		add = high_digit(add);
	}
	template <typename _Tx, typename _Ty> static inline void borrow(_Tx &add, _Ty &baseval, _Tx newval) {
		add += newval - COMPRESS_MOD + 1;
		baseval = (_Tx)low_digit(add) + COMPRESS_MOD - 1;
		add = high_digit(add);
	}

	bool raw_less(const BigInt_t &b) const {
		if (v.size() != b.size()) return v.size() < b.size();
		for (size_t i = v.size() - 1; i < v.size(); i--)
			if (v[i] != b.v[i]) return v[i] < b.v[i];
		return false; // eq
	}
	bool raw_eq(const BigInt_t &b) const {
		if (this == &b) return true;
		if (v.size() != b.size()) return false;
		for (size_t i = 0; i < v.size(); ++i)
			if (v[i] != b.v[i]) return false;
		return true;
	}
	BigInt_t &raw_add(const BigInt_t &b) {
		if (v.size() < b.size()) v.resize(b.size());
		ucarry_t add = 0;
		for (size_t i = 0; i < b.v.size(); i++)
			carry(add, v[i], (ucarry_t)(v[i] + b.v[i]));
		for (size_t i = b.v.size(); add && i < v.size(); i++)
			carry(add, v[i], (ucarry_t)v[i]);
		add ? v.push_back((base_t)add) : trim();
		return *this;
	}
	BigInt_t &raw_offset_add(const BigInt_t &b, size_t offset) {
		ucarry_t add = 0;
		for (size_t i = 0; i < b.size(); ++i)
			carry(add, v[i + offset], (ucarry_t)(v[i + offset] + b.v[i]));
		for (size_t i = b.size() + offset; add; ++i)
			carry(add, v[i], (ucarry_t)v[i]);
		return *this;
	}
	BigInt_t &raw_sub(const BigInt_t &b) {
		if (v.size() < b.v.size()) v.resize(b.v.size());
		carry_t add = 0;
		for (size_t i = 0; i < b.v.size(); i++)
			borrow(add, v[i], (carry_t)v[i] - (carry_t)b.v[i]);
		for (size_t i = b.v.size(); add && i < v.size(); i++)
			borrow(add, v[i], (carry_t)v[i]);
		if (add) {
			sign = -sign;
			add = 1;
			for (size_t i = 0; i < v.size(); i++)
				carry(add, v[i], (carry_t)(COMPRESS_MOD - v[i] - 1));
		}
		trim();
		return *this;
	}
	BigInt_t &raw_offset_mulsub(const BigInt_t &b, base_t mul, size_t offset) {
		if (mul == 0) return *this;
		carry_t add = 0;
		for (size_t i = 0; i < b.v.size(); i++)
			borrow(add, v[i + offset], (carry_t)v[i + offset] - (carry_t)b.v[i] * (carry_t)mul);
		for (size_t i = offset + b.v.size(); add && i < v.size(); i++)
			borrow(add, v[i], (carry_t)v[i]);
		return *this;
	}
	BigInt_t &raw_mul_int(base_t m) {
		if (m == 0) {
			set(0);
			return *this;
		} else if (m == 1)
			return *this;
		ucarry_t add = 0;
		size_t i = 0;
		for (; i + 4 <= v.size(); i += 4) {
			carry(add, v[i], v[i] * (ucarry_t)m);
			carry(add, v[i + 1], v[i + 1] * (ucarry_t)m);
			carry(add, v[i + 2], v[i + 2] * (ucarry_t)m);
			carry(add, v[i + 3], v[i + 3] * (ucarry_t)m);
		}
		for (; i < v.size(); i++)
			carry(add, v[i], v[i] * (ucarry_t)m);
		if (add) v.push_back((base_t)add);
		return *this;
	}
	BigInt_t &raw_mul(const BigInt_t &a, const BigInt_t &b) {
		if (a.is_zero() || b.is_zero()) {
			return set(0);
		}
		if (a.size() == 1 && a.v[0] == 1) {
			*this = b;
			sign *= a.sign;
			return *this;
		}
		if (b.size() == 1 && b.v[0] == 1) {
			*this = a;
			sign *= b.sign;
			return *this;
		}
		if (a.size() == 2 && a.v[1] == 1 && a.v[0] == 0) {
			*this = b;
			raw_shl(1);
			sign *= a.sign;
			return *this;
		}
		if (b.size() == 2 && b.v[1] == 1 && b.v[0] == 0) {
			*this = a;
			raw_shl(1);
			sign *= b.sign;
			return *this;
		}
		v.clear();
		v.resize(a.size() + b.size());
		for (size_t i = 0; i < a.size(); i++) {
			ucarry_t add = 0, av = a.v[i];
			size_t j = 0;
			for (; j + 4 <= b.size(); j += 4) {
				carry(add, v[i + j], v[i + j] + av * b.v[j]);
				carry(add, v[i + j + 1], v[i + j + 1] + av * b.v[j + 1]);
				carry(add, v[i + j + 2], v[i + j + 2] + av * b.v[j + 2]);
				carry(add, v[i + j + 3], v[i + j + 3] + av * b.v[j + 3]);
			}
			for (; j < b.size(); ++j) {
				carry(add, v[i + j], v[i + j] + av * b.v[j]);
			}
			v[i + b.size()] += (base_t)add;
		}
		trim();
		return *this;
	}
	BigInt_t &raw_mul_karatsuba(const BigInt_t &a, const BigInt_t &b) {
		if (std::min(a.size(), b.size()) <= BIGINT_MUL_THRESHOLD) {
			return raw_mul(a, b);
		}
		if (a.size() * 2 < b.size() || b.size() * 2 < a.size()) { // split
			BigInt_t t;
			if (a.size() < b.size()) {
				size_t split = b.size() / 2;
				t.raw_mul_karatsuba(a, b.raw_shr_to(split));
				t.raw_shl(split);
				raw_mul_karatsuba(a, b.raw_lowdigits_to(split));
				raw_add(t);
			} else {
				size_t split = a.size() / 2;
				t.raw_mul_karatsuba(b, a.raw_shr_to(split));
				t.raw_shl(split);
				raw_mul_karatsuba(b, a.raw_lowdigits_to(split));
				raw_add(t);
			}
			return *this;
		}
		if (std::min(a.size(), b.size()) <= BIGINT_NTT_THRESHOLD)
			;
		else if ((a.size() + b.size()) <= NTT_MAX_SIZE)
			return raw_nttmul(a, b);
		BigInt_t ah, al, bh, bl, h, m;
		size_t split = std::max(std::min((a.size() + 1) / 2, b.size() - 1), std::min(a.size() - 1, (b.size() + 1) / 2));
		al.v.assign(a.v.begin(), a.v.begin() + split);
		ah.v.assign(a.v.begin() + split, a.v.end());
		bl.v.assign(b.v.begin(), b.v.begin() + split);
		bh.v.assign(b.v.begin() + split, b.v.end());

		raw_mul_karatsuba(al, bl);
		h.raw_mul_karatsuba(ah, bh);
		m.raw_mul_karatsuba(al + ah, bl + bh);
		m.raw_sub(*this);
		m.raw_sub(h);
		v.resize(a.size() + b.size());

		raw_offset_add(m, split);
		raw_offset_add(h, split * 2);
		trim();
		return *this;
	}
	BigInt_t &raw_nttmul(const BigInt_t &a, const BigInt_t &b) {
		if (std::min(a.size(), b.size()) <= BIGINT_MUL_THRESHOLD) {
			return raw_mul(a, b);
		}
		if (std::min(a.size(), b.size()) <= BIGINT_NTT_THRESHOLD || (a.size() + b.size()) > NTT_MAX_SIZE) {
			return raw_mul_karatsuba(a, b);
		}
		if (a.size() * 3 < b.size() || b.size() * 3 < a.size()) { // split
			BigInt_t t;
			if (a.size() < b.size()) {
				size_t split = b.size() / 2;
				t.raw_nttmul(a, b.raw_shr_to(split));
				t.raw_shl(split);
				raw_nttmul(a, b.raw_lowdigits_to(split));
				raw_add(t);
			} else {
				size_t split = a.size() / 2;
				t.raw_nttmul(b, a.raw_shr_to(split));
				t.raw_shl(split);
				raw_nttmul(b, a.raw_lowdigits_to(split));
				raw_add(t);
			}
			return *this;
		}
		size_t len;
		std::vector<NTT_NS::ntt_base_t> &ntt_a = NTT_NS::ntt1.ntt_a, &ntt_b = NTT_NS::ntt1.ntt_b;
		std::vector<int64_t> &ntt_c = NTT_NS::ntt1.ntt_c;
#if BIGINT_LARGE_BASE
		ntt_a.resize(a.size() * 2);
		ntt_b.resize(b.size() * 2);
		for (size_t i = 0, j = 0; i < a.size(); ++i, ++j) {
			ntt_a[j] = a.v[i] % COMPRESS_HALF_MOD;
			ntt_a[++j] = a.v[i] / COMPRESS_HALF_MOD;
		}
		if (a == b) {
			NTT_NS::ntt_prepare(a.size() * 2, a.size() * 2, len, 7);
			NTT_NS::sqr_conv();
			len = a.size() * 4;
		} else {
			for (size_t i = 0, j = 0; i < b.size(); ++i, ++j) {
				ntt_b[j] = b.v[i] % COMPRESS_HALF_MOD;
				ntt_b[++j] = b.v[i] / COMPRESS_HALF_MOD;
			}
			NTT_NS::ntt_prepare(a.size() * 2, b.size() * 2, len, 7);
			NTT_NS::mul_conv();
			len = (a.size() + b.size()) * 2;
		}
#else
		ntt_a.resize(a.size());
		ntt_b.resize(b.size());
		for (size_t i = 0; i < a.size(); ++i) {
			ntt_a[i] = a.v[i];
		}
		if (a == b) {
			NTT_NS::ntt_prepare(a.size(), a.size(), len, 7);
			NTT_NS::sqr_conv();
			len = a.size() * 2;
		} else {
			for (size_t i = 0; i < b.size(); ++i) {
				ntt_b[i] = b.v[i];
			}
			NTT_NS::ntt_prepare(a.size(), b.size(), len, 7);
			NTT_NS::mul_conv();
			len = a.size() + b.size();
		}
#endif
		while (len > 0 && ntt_c[--len] == 0)
			;
		v.clear();
		uint64_t add = 0;
#if BIGINT_LARGE_BASE
		v.reserve(++len / 2 + 2);
		for (size_t i = 0; i < len; i += 2) {
			add += ntt_c[i] + (ntt_c[i + 1] * COMPRESS_HALF_MOD);
			v.push_back(low_digit(add));
			add = high_digit(add);
		}
#else
		v.reserve(len + 3);
		for (size_t i = 0; i <= len; i++) {
			add += ntt_c[i];
			v.push_back(low_digit(add));
			add = high_digit(add);
		}
#endif
		for (; add; add = high_digit(add))
			v.push_back(low_digit(add));
		trim();
		return *this;
	}
	BigInt_t &raw_div(const BigInt_t &a, const BigInt_t &b, BigInt_t &r) {
		r = a;
		if (a.raw_less(b)) {
			return set(0);
		} else if (b.size() == 2 && b.v[1] == 1 && b.v[0] == 0) {
			*this = a;
			r.set(a.v[0]);
			return raw_shr(1);
		}
		v.clear();
		v.resize(a.size() - b.size() + 1);
		r.v.resize(a.size() + 1);
		size_t offset = b.size();
		double db = b.v.back();
#if BIGINT_LARGE_BASE
		if (b.size() > 2) {
			double t = b.v[b.size() - 2] + b.v[b.size() - 3] / (double)COMPRESS_MOD;
			db += (b.v.back() / (double)COMPRESS_HALF_MOD + t) / COMPRESS_MOD;
		} else if (b.size() > 1) {
			db += (b.v.back() / (double)COMPRESS_HALF_MOD + b.v[b.size() - 2]) / COMPRESS_MOD;
		}
#else
		if (b.size() > 2) {
			db += (b.v[b.size() - 2] + (b.v[b.size() - 3] + 1) / (double)COMPRESS_MOD) / COMPRESS_MOD;
		} else if (b.size() > 1) {
			db += b.v[b.size() - 2] / (double)COMPRESS_MOD;
		}
#endif
		db = 1 / db;
		for (size_t i = a.size() - offset, j = a.size() - 1; i <= a.size();) {
			carry_t rm = (carry_t)r.v[j + 1] * COMPRESS_MOD + r.v[j], m;
			m = std::max((carry_t)(rm * db), (carry_t)r.v[i + offset]);
			v[i] += (base_t)m;
			r.raw_offset_mulsub(b, (base_t)m, i);
			if (!r.v[j + 1]) --i, --j;
		}
		r.trim();
		carry_t add = 0;
		while (!r.raw_less(b)) {
			r.raw_sub(b);
			++add;
		}

		for (size_t i = 0; i < v.size(); i++)
			carry(add, v[i], (carry_t)v[i]);
		trim();
		return *this;
	}
	BigInt_t &raw_shr(size_t n) {
		if (n == 0) return *this;
		if (n >= size()) {
			set(0);
			return *this;
		}
		v.erase(v.begin(), v.begin() + n);
		return *this;
	}
	BigInt_t raw_shr_to(size_t n) const {
		BigInt_t r;
		if (n >= size()) return r;
		r.v.assign(v.begin() + n, v.end());
		return BIGINT_STD_MOVE(r);
	}
	BigInt_t raw_lowdigits_to(size_t n) const {
		if (n >= size()) return *this;
		BigInt_t r;
		r.v.assign(v.begin(), v.begin() + n);
		r.trim();
		return BIGINT_STD_MOVE(r);
	}
	BigInt_t &raw_shl(size_t n) {
		if (n == 0 || is_zero()) return *this;
		v.insert(v.begin(), n, 0);
		return *this;
	}
	BigInt_t &keep(size_t n) {
		size_t s = n < v.size() ? v.size() - n : (size_t)0;
		if (s && v[s - 1] >= COMPRESS_MOD >> 1) ++v[s];
		return raw_shr(s);
	}
	BigInt_t &raw_fastdiv(const BigInt_t &a, const BigInt_t &b) {
		if (a.raw_less(b)) {
			set(0);
			return *this;
		}
		if (b.size() * 2 - 2 > a.size()) {
			BigInt_t ta = a, tb = b;
			size_t ans_len = a.size() - b.size() + 2;
			size_t r = b.size() - ans_len;
			ta.raw_shr(r);
			tb.raw_shr(r);
			return raw_fastdiv(ta, tb);
		}
		if (b.size() < BIGINT_DIV_THRESHOLD) {
			BigInt_t r;
			return raw_div(a, b, r);
		}
		size_t extand_digs = 2;
		size_t ans_len = a.size() - b.size() + extand_digs + 1, s_len = ans_len + 32;
		std::vector<size_t> len_seq;
		BigInt_t b2, x0, x1, t;
		x1.v.resize(1);
		x1.v.back() = (base_t)(COMPRESS_MOD / (b.v.back() + (double)(b.v[b.size() - 2]) / COMPRESS_MOD));
		x0.v.push_back(x1.v.back() + 1);
		size_t keep_size = 1;
		while (s_len > 32) {
			len_seq.push_back(std::min(s_len, ans_len));
			s_len = s_len / 2 + 1;
		}
		while (x1 != x0) {
			x0 = x1;
			b2 = b;
			size_t tsize = std::min(keep_size * 2, ans_len);
			b2.keep(tsize);
			t = x0 * b2;
			t.keep(tsize);
			for (size_t i = t.size() - 2; i < t.size(); --i)
				t.v[i] = COMPRESS_MOD - 1 - t.v[i];
			if (t.v.back() != 1) {
				t.v.back() = COMPRESS_MOD - 1 - t.v.back();
				t.v.push_back(1);
			} else {
				t.v.pop_back();
				t.trim();
			}
			x1 *= t;
			keep_size = std::min(keep_size * 2, s_len);
			x1.keep(keep_size);
		}
		for (; !len_seq.empty(); len_seq.pop_back()) {
			x0 = x1;
			b2 = b;
			size_t tsize = std::min(keep_size * 2, ans_len);
			b2.keep(tsize);
			t = x0 * b2;
			t.keep(tsize);
			for (size_t i = t.size() - 2; i < t.size(); --i)
				t.v[i] = COMPRESS_MOD - 1 - t.v[i];
			if (t.v.back() != 1) {
				t.v.back() = COMPRESS_MOD - 1 - t.v.back();
				t.v.push_back(1);
			} else {
				t.v.pop_back();
				t.trim();
			}
			ucarry_t add = 1;
			for (size_t i = 0; add && i < t.v.size(); i++)
				carry(add, t.v[i], (ucarry_t)t.v[i]);
			if (add) t.v.push_back((base_t)add);
			x1 *= t;
			keep_size = len_seq.back();
			x1.keep(keep_size);
		}
		x1 *= a;
		if (x1.v[a.size() + extand_digs - 1] >= COMPRESS_MOD - 1)
			*this = x1.raw_shr(a.size() + extand_digs).raw_add(BigInt_t(1));
		else
			*this = x1.raw_shr(a.size() + extand_digs);
		return *this;
	}
	BigInt_t &raw_dividediv_recursion(const BigInt_t &a, const BigInt_t &b, BigInt_t &r) {
		if (a < b) {
			r = a;
			return set(0);
		} else if (b.size() <= BIGINT_DIVIDEDIV_THRESHOLD) {
			return raw_div(a, b, r);
		}
		size_t base = (b.size() + 1) / 2;
		if (a.size() <= base * 3) {
			base = b.size() / 2;
			BigInt_t ma = a, mb = b, e;
			BigInt_t ha = ma.raw_shr_to(base);
			BigInt_t hb = mb.raw_shr_to(base);
			raw_dividediv_recursion(ha, hb, r);
			ha = *this * b;
			while (a < ha) {
				ha.raw_sub(b);
				raw_sub(BigInt_t(1));
			}
			r = a - ha;
			return *this;
		}
		if (a.size() > base * 4) base = a.size() / 2;
		BigInt_t ha = a.raw_shr_to(base);
		BigInt_t c, d, m;
		raw_dividediv_recursion(ha, b, d);
		raw_shl(base);
		m.v.resize(base + d.size());
		for (size_t i = 0; i < base; ++i)
			m.v[i] = a.v[i];
		for (size_t i = 0; i < d.size(); ++i)
			m.v[base + i] = d.v[i];
		c.raw_dividediv_recursion(m, b, r);
		raw_add(c);
		return *this;
	}
	BigInt_t &raw_dividediv(const BigInt_t &a, const BigInt_t &b, BigInt_t &r) {
		if (b.size() <= BIGINT_DIVIDEDIV_THRESHOLD) {
			raw_div(a, b, r);
			return *this;
		}
		if (b.size() * 2 - 2 > a.size()) {
			BigInt_t ta = a, tb = b;
			size_t ans_len = a.size() - b.size() + 2;
			size_t shr = b.size() - ans_len;
			ta.raw_shr(shr);
			tb.raw_shr(shr);
			return raw_dividediv(ta, tb, r);
		}
		carry_t mul = (carry_t)(((uint64_t)(COMPRESS_MOD + 1) * (COMPRESS_MOD - 1)) /	   //
								(*(b.v.begin() + b.v.size() - 1) * (uint64_t)COMPRESS_MOD + //
								 *(b.v.begin() + b.v.size() - 2) + 1));
		BigInt_t ma = a * BigInt_t((intmax_t)mul), mb = b * BigInt_t((intmax_t)mul);
		while (mb.v.back() < COMPRESS_MOD >> 1) {
			int32_t m = 2;
			ma.raw_mul_int(m);
			mb.raw_mul_int(m);
			mul *= m;
		}
		BigInt_t d;
		ma.sign = mb.sign = 1;
		raw_dividediv_recursion(ma, mb, d);
		r.raw_div(d, BigInt_t((int)mul), ma);
		return *this;
	}
	void trim() {
		while (v.back() == 0 && v.size() > 1)
			v.pop_back();
	}
	size_t size() const { return v.size(); }
	std::string out_dec() const {
		if (is_zero()) return "0";
		std::string out;
		int32_t d = 0;
		for (size_t i = 0, j = 0;;) {
			if (j < 1) {
				if (i < size())
					d += v[i];
				else if (d == 0)
					break;
				j += COMPRESS_DIGITS;
				++i;
			}
			out.push_back((d % 10) + '0');
			d /= 10;
			j -= 1;
		}
		while (out.size() > 1 && *out.rbegin() == '0')
			out.erase(out.begin() + out.size() - 1);
		if (sign < 0 && !this->is_zero()) out.push_back('-');
		std::reverse(out.begin(), out.end());
		return out;
	}
	BigInt_t &from_str_base10(const char *s) {
		v.clear();
		int32_t base = 10, sign = 1, digits = COMPRESS_DIGITS;
		const char *p = s + strlen(s) - 1;
		while (*s == '-')
			sign *= -1, ++s;
		while (*s == '0')
			++s;

		int64_t d = digits, hdigit = 0, hdigit_mul = 1;
		for (; p >= s; p--) {
			hdigit += (*p - '0') * hdigit_mul;
			hdigit_mul *= base;
			if (--d == 0) {
				v.push_back((base_t)hdigit);
				d = digits;
				hdigit = 0;
				hdigit_mul = 1;
			}
		}
		if (hdigit || v.empty()) {
			v.push_back((base_t)hdigit);
		}
		this->sign = sign;
		return *this;
	}
public:
	BigIntDec() { set(0); }
	explicit BigIntDec(int n) { set(n); }
	explicit BigIntDec(intmax_t n) { set(n); }
	explicit BigIntDec(const char *s) { from_str(s); }
	explicit BigIntDec(const std::string &s) { from_str(s); }
	BigInt_t &set(intmax_t n) {
		v.resize(1);
		v[0] = 0;
		uintmax_t s;
		if (n < 0) {
			sign = -1;
			s = -n;
		} else {
			sign = 1;
			s = n;
		}
		for (size_t i = 0; s; i++) {
			v.resize(i + 1);
			v[i] = low_digit(s);
			s = high_digit(s);
		}
		return *this;
	}
	BigInt_t &set_bysize(size_t size) {
		v.resize(size? size: 1);
		*v.rbegin() = 1;
		return *this;
	}
	BigInt_t &from_str(const char *s) {
			return from_str_base10(s);
	}
	BigInt_t &from_str(const std::string &s) { return this->from_str(s.c_str()); }
	base_t get_v(size_t i) const { return v[i]; }
	size_t get_size() const { return v.size(); }
	int get_sign() const { return sign; }
	bool is_zero() const {
		if (v.size() == 1 && v[0] == 0) return true;
		return false;
	}
	bool operator<(const BigInt_t &b) const {
		if (sign * b.sign > 0) {
			if (sign > 0)
				return raw_less(b);
			else
				return b.raw_less(*this);
		} else {
			if (sign > 0)
				return false;
			else
				return true;
		}
	}
	bool operator==(const BigInt_t &b) const {
		if (is_zero() && b.is_zero()) return true;
		if (sign != b.sign) return false;
		return raw_eq(b);
	}
	bool operator>(const BigInt_t &b) const { return b < *this; }
	bool operator<=(const BigInt_t &b) const { return !(b < *this); }
	bool operator>=(const BigInt_t &b) const { return !(*this < b); }
	bool operator!=(const BigInt_t &b) const { return !(*this == b); }

	BigInt_t &operator=(intmax_t n) { return set(n); }
	BigInt_t &operator=(const char *s) { return from_str(s); }
	BigInt_t &operator=(const std::string s) { return from_str(s); }
	BigInt_t operator+(const BigInt_t &b) const {
		if (sign * b.sign > 0)
			return BIGINT_STD_MOVE(BigInt_t(*this).raw_add(b));
		else if (size() < b.size())
			return BIGINT_STD_MOVE(BigInt_t(b).raw_sub(*this).inv());
		else
			return BIGINT_STD_MOVE(BigInt_t(*this).raw_sub(b));
	}
	BigInt_t &operator+=(const BigInt_t &b) {
		if (this == &b)
			return *this += BigInt_t(b);
		if (sign * b.sign > 0)
			raw_add(b);
		else if (size() < b.size())
			*this = BIGINT_STD_MOVE(BigInt_t(b).raw_sub(*this).inv());
		else
			raw_sub(b);
		return *this;
	}

	BigInt_t operator-(const BigInt_t &b) const {
		if (sign * b.sign < 0)
			return BIGINT_STD_MOVE(BigInt_t(*this).raw_add(b));
		else if (size() < b.size())
			return BIGINT_STD_MOVE(BigInt_t(b).raw_sub(*this).inv());
		else
			return BIGINT_STD_MOVE(BigInt_t(*this).raw_sub(b));
	}
	BigInt_t &operator-=(const BigInt_t &b) {
		if (this == &b) {
			set(0);
			return *this;
		}
		if (sign * b.sign < 0)
			raw_add(b);
		else if (size() < b.size())
			*this = BIGINT_STD_MOVE(BigInt_t(b).raw_sub(*this).inv());
		else
			raw_sub(b);
		return *this;
	}
	BigInt_t& inv() {
		sign = -sign;
		return *this;
	}
	BigInt_t operator-() const {
		return BIGINT_STD_MOVE(BigInt_t(*this).inv());
	}

	BigInt_t operator*(const BigInt_t &b) const {
		if (b.size() == 1) {
			BigInt_t r = *this;
			r.raw_mul_int((uint32_t)b.v[0]);
			r.sign *= b.sign;
			return BIGINT_STD_MOVE(r);
		} else if (v.size() == 1) {
			BigInt_t r = b;
			r.raw_mul_int((uint32_t)v[0]);
			r.sign *= sign;
			return BIGINT_STD_MOVE(r);
		} else {
			BigInt_t r;
			if (raw_less(b))
				r.raw_nttmul(*this, b);
			else
				r.raw_nttmul(b, *this);
			r.sign = sign * b.sign;
			return BIGINT_STD_MOVE(r);
		}
	}
	BigInt_t &operator*=(const BigInt_t &b) {
		if (b.size() == 1) {
			raw_mul_int((uint32_t)b.v[0]);
			sign *= b.sign;
			return *this;
		} else {
			return *this = *this * b;
		}
	}

	BigInt_t operator/(const BigInt_t &b) const {
		BigInt_t r, d;
		if (b.size() > BIGINT_DIV_THRESHOLD)
			d.raw_fastdiv(*this, b);
		else
			d.raw_dividediv(*this, b, r);
		d.sign = sign * b.sign;
		return BIGINT_STD_MOVE(d);
	}
	BigInt_t &operator/=(const BigInt_t &b) {
		if (this == &b) {
			return set(1);
		}
		return *this = *this / b;
	}
	BigInt_t operator%(const BigInt_t &b) const {
		if (b.size() == 1 && COMPRESS_MOD % b.v[0] == 0) {
			return BigInt_t((intmax_t)(v[0] % b.v[0]) * sign);
		}
		if (this == &b) {
			return BigInt_t((intmax_t)0);
		}
		return BIGINT_STD_MOVE(*this - *this / b * b);
	}
	BigInt_t &operator%=(const BigInt_t &b) {
		if (b.size() == 1 && COMPRESS_MOD % b.v[0] == 0) {
			return set(v[0] % b.v[0] * sign);
		}
		if (this == &b) {
			return set(0);
		}
		return *this = *this % b;
	}
	BigInt_t div(const BigInt_t &b, BigInt_t &r) {
		if (this == &b) {
			r.set(0);
			return set(1);
		}
		BigInt_t d;
		d.raw_fastdiv(*this, b);
		d.sign = sign * b.sign;
		r = *this - d * b;
		return BIGINT_STD_MOVE(d);
	}

	std::string to_str() const {
		return out_dec();
	}
};
} // namespace BigIntDecNS

using BigIntDecNS::BigIntDec;

typedef BigIntDec BigInt;
