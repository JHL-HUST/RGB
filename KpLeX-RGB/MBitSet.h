#pragma once
#include <assert.h>
#include <nmmintrin.h>
#include <algorithm>
#include <cstdint>

#ifdef __SSE2__
#include <immintrin.h>
#include <malloc.h>
#define AllocBuf(sz) _mm_malloc((sz), 16)
#define FreeBuf(ptr) _mm_free(ptr)
#else
#define AllocBuf(sz) malloc(sz)
#define FreeBuf(ptr) free(ptr);
#endif

/*Improve the performance with 64-bit machine*/
static unsigned char BitsSetTable256[256] =
{
#   define B2(n) n,     n+1,     n+1,     n+2
#   define B4(n) B2(n), B2(n+1), B2(n+1), B2(n+2)
#   define B6(n) B4(n), B4(n+1), B4(n+1), B4(n+2)
	B6(0), B6(1), B6(1), B6(2)
}; 

static inline int countUI32(const uint32_t &v) {
	return BitsSetTable256[v & 0xff] +
		BitsSetTable256[(v >> 8) & 0xff] +
		BitsSetTable256[(v >> 16) & 0xff] +
		BitsSetTable256[v >> 24];
}

static inline int countUI64(const uint64_t &v) {
	return BitsSetTable256[v & 0xffULL] +
		BitsSetTable256[(v >> 8) & 0xffULL] +
		BitsSetTable256[(v >> 16) & 0xffULL] +
		BitsSetTable256[(v >> 24) & 0xffULL] +
		BitsSetTable256[(v >> 32) & 0xff] +
		BitsSetTable256[(v >> 40) & 0xff] +
		BitsSetTable256[v >> 48 & 0xff] +
		BitsSetTable256[v >> 56];	
}


class MBitSet64 {
private:
	int n; // the size of buff is n+1
	int m;	// valid sz in last int
	int cap;
	uint64_t *buf;
public:
	MBitSet64(){
		cap = n = m = 0;
		buf = nullptr;
	
	}
	MBitSet64(int range){
		m = range & 63;	// n%63
		n = range >> 6; //	n/64
		cap = range;
		
		buf = new uint64_t[n + 1];
		for (int i = 0; i <= n; ++i)
			buf[i] = 0ULL;
	}
	MBitSet64(const MBitSet64& mbs) {
		n = mbs.n;
		m = mbs.m;
		cap = mbs.cap;

		if (buf != nullptr) 
			delete[] buf;
		buf = new uint64_t[n + 1];
		for (int i = 0; i <= n; i++) {
			buf[i] = mbs.buf[i];
		}
	}
	//Assign function
	MBitSet64& operator=(const MBitSet64& mbs) {
		n = mbs.n;
		m = mbs.m;
		cap = mbs.cap;
		if (buf != nullptr)
			delete[] buf;		
		buf = new uint64_t[n + 1];
		for (int i = 0; i <= n; i++)
			buf[i] = mbs.buf[i];
		return (*this);
	}

	~MBitSet64() {
		if (buf != nullptr)
			delete[] buf;
	}
	void clear() {
		for (int i = 0; i <= n; i++)
			buf[i] = 0ULL;
	}
	void flip() {
		for (int i = 0; i < n; ++i)
			buf[i] = ~buf[i];
		buf[n] ^= (1ULL << m) - 1;
	}

	void set(int x) {
		//assert(x < cap);
		buf[x >> 6] ^= 1ULL << (x & 63);
	}
	
	bool test(int x) {
		return buf[x >> 6] >> (x & 63) & 1ULL;
	}

	bool empty() {
		for (int i = 0; i <= n; ++i)
			if (buf[i])
				return false;
		return true;
	}

	void operator &=(const MBitSet64 &rhs) {
		assert(n == rhs.n);
		for (int i = 0; i <= n; ++i)
			buf[i] &= rhs.buf[i];
	}
	int size() {
		int sum = 0;
		for (int i = 0; i <= n; i++){
			//sum += countUI64(buf[i]);
			sum += _mm_popcnt_u64(buf[i]);
		}
		return sum;
	}

	/*return the size of intersection */
	int intersect(const MBitSet64 &mbs) {
		int sum = 0;
		for (int i = 0; i <= n; i++) {
			//sum += countUI64(buf[i] & mbs.buf[i]);
			sum += _mm_popcnt_u64(buf[i] & mbs.buf[i]);
		}
		return sum;
	}
	

};

class MBitSet32 {
private:
	int n, m; //n number of uint64, m the number of valid bits in the last int
	int cap;	//maximum supported value.
	uint32_t *buf;

public:
	MBitSet32() {
		buf = nullptr;
		cap = n = m = 0;
	}
	//range: the maximum supported value (including range) [0,range]
	MBitSet32(int range) {
		m = range & 31;	// n%32
		n = range >> 5; //	n/32
		cap = range;
		buf = (uint32_t*)AllocBuf((n + 1) * sizeof(uint32_t));
		for (int i = 0; i <= n; ++i)
			buf[i] = 0;
	}
	MBitSet32& operator=(const MBitSet32& mbs) {
		n = mbs.n;
		m = mbs.m;
		cap = mbs.cap;
		if (buf != nullptr)
			FreeBuf(buf);
		buf = new uint32_t[n + 1];
		for (int i = 0; i <= n; i++)
			buf[i] = mbs.buf[i];
		return (*this);
	}

	~MBitSet32() {
		if (buf != nullptr)
			FreeBuf(buf);
	}

	void clear() {
		for (int i = 0; i <= n; i++)
			buf[i] = 0;
	}

	//copy constructor
	MBitSet32(const MBitSet32& mbs) {
		n = mbs.n;
		m = mbs.m;
		cap = mbs.cap;
		if (buf != nullptr)
			FreeBuf(buf);
		buf = new uint32_t[n + 1];
		for (int i = 0; i <= n; i++) {
			buf[i] = mbs.buf[i];
		}
	}
	//FLIP all the bits
	void flip() {
		for (int i = 0; i < n; ++i)
			buf[i] = ~buf[i];
		buf[n] ^= ((unsigned)1 << m) - 1;
	}
	
	void set(int x) {
		//assert(x < cap);
		buf[x >> 5] ^= (unsigned)1 << (x & 31);
	}
	bool test(int x) {
		return buf[x >> 5] >> (x & 31) & 1;
	}

	bool empty() {
		for (int i = 0; i <= n; ++i)
			if (buf[i])
				return false;
		return true;
	}
	void operator &=(const MBitSet32 &rhs) {
		for (int i = 0; i <= n; ++i)
			this->buf[i] &= rhs.buf[i];
	} 

	int size() {
		int sum = 0;
		for (int i = 0; i <= n; i++) {
			//sum += countUI32(buf[i]);
			sum += _mm_popcnt_u32(buf[i]);
		}
		return sum;
	}

	/*return the size of intersection */
	int intersect(const MBitSet32 &mbs) {
		int sum = 0;
		for (int i = 0; i <= n; i++) {
			//sum += countUI32(buf[i] & mbs.buf[i]);
			sum += _mm_popcnt_u32(buf[i] & mbs.buf[i]);
		}
		return sum;
	}

}; 
