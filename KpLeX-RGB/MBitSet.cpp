/**
 * This file is for test purpose.
 * */
#include <stdio.h>
#include "MBitSet.h"
#include <time.h>


void testMBitSet() {
	printf("size of %d\n", sizeof(unsigned));
	printf("size of %d\n", 1 << 16);
	printf("size of unsigned in %d\n", sizeof(unsigned int));
	//printf("NB nodes %d\n", kplex.nbvtx);

	MBitSet32 mbs(100);
	//mbs.allocacte(100);
	//mbs.reinit(100);
	mbs.set(0);
	//mbs.set(1);
	mbs.set(3);
	mbs.set(13);
	mbs.set(99);
	mbs.set(100);

	MBitSet32 mbs2(100);
	//mbs2.allocacte(100);
	//mbs2.reinit(100);
	mbs2.set(100);
	mbs2.set(0);
	mbs2.set(13);
	printf("size of intersection %d\n", mbs.intersect(mbs2));
}
void testMBitSet64() {
	printf("size of %d\n", sizeof(unsigned));
	printf("size of %d\n", 1 << 16);
	printf("size of unsigned in %d\n", sizeof(unsigned int));
	//printf("NB nodes %d\n", kplex.nbvtx);

	MBitSet64 mbs(100);
	mbs.set(0);
	//mbs.set(1);
	mbs.set(3);
	mbs.set(13);
	mbs.set(99);
	mbs.set(100);

	MBitSet64 mbs2(100);	
	mbs2.set(100);
	mbs2.set(0);
	mbs2.set(13);
	printf("size of intersection %d\n", mbs.intersect(mbs2));

}

void testCompare() {
	const int MAXRANGE = 500;
	//const int MAXRANGE = 10;
	const int NB_SETS = 900000;
	//const int NB_SETS = 4;
	const int SZ_SET = 300;
	//const int SZ_SET = 7;
	int **elems = new int*[NB_SETS];
	for (int i = 0; i < NB_SETS; i++) {
		elems[i] = new int[SZ_SET];
		for (int j = 0; j < SZ_SET; j++) {
			elems[i][j] = rand() % MAXRANGE;
		}
	}	
	MBitSet32 *mbs32 = new MBitSet32[NB_SETS];
	for (int i = 0; i < NB_SETS; i++) {
		mbs32[i] = MBitSet32(MAXRANGE);
		for (int j = 0; j < SZ_SET; j++)
			if (!mbs32[i].test(elems[i][j]))
				mbs32[i].set(elems[i][j]);	
	}

	MBitSet64 *mbs64 = new MBitSet64[NB_SETS];
	for (int i = 0; i < NB_SETS; i++) {
		mbs64[i] = MBitSet64(MAXRANGE);
		for (int j = 0; j < SZ_SET; j++)
			if (!mbs64[i].test(elems[i][j]))
				mbs64[i].set(elems[i][j]);
	}

	/*for (int i = 0; i < NB_SETS; i++) {
		//assert(mbs32[i].size() == mbs64[i].size());
		std::sort(elems[i], elems[i] + SZ_SET);
		int* end = std::unique(elems[i], elems[i] + SZ_SET);
		assert(mbs64[i].size() == std::distance(elems[i], end));
	}*/
		

	int *nbSame1 = new int[NB_SETS-1];
	clock_t clkStart1 = clock();
	for (int i = 0; i < NB_SETS - 1; i++) {
		nbSame1[i] = mbs32[i].intersect(mbs32[i + 1]);
	}
	clock_t clkEnd1 = clock();
	printf("32 bit intersect: %.3llf\n", (double)(clkEnd1 - clkStart1) / CLOCKS_PER_SEC);


	int *nbSame2 = new int[NB_SETS - 1];
	clock_t clkStart2 = clock();
	for (int i = 0; i < NB_SETS - 1; i++) {
		nbSame2[i] = mbs64[i].intersect(mbs64[i + 1]);
	}
	clock_t clkEnd2 = clock();
	printf("64 bit intersect: %.3llf\n", (double)(clkEnd2 - clkStart2) / CLOCKS_PER_SEC);

	for (int i = 0; i < NB_SETS - 1; i++){
		/*
		if (nbDiffer1[i] != nbDiffer2[i]) {
			printf("%d - %d\n", nbDiffer1[i], nbDiffer2[i]);
			for (int j = 0; j < SZ_SET; j++) {
				printf("%d ", elems[i][j]);
			}
			printf("\n");
			for (int j = 0; j < SZ_SET; j++) {
				printf("%d ", elems[i+1][j]);
			}
			printf("\n");
		}*/
		assert(nbSame1[i] == nbSame2[i]);
	}
}

void testCount() {
	uint64_t v1= 0x0fe0000000000000ULL;
	printf("%d\n", countUI64(v1));
}
int __main__() {
//	testMBitSet();
//	testMBitSet64();
	testCompare();
	//testCount();
	return 0;
}