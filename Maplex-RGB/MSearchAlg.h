#pragma once
#include <algorithm>
#include "MGraph.h"
#include "LinearHeap.h"
using namespace std;

class FastExactSearch{
public:
	//const MCsrGraph &cg;
    MBitGraph *bg;
	MBitGraph *rbg;
    int K;
    int lb;
	int maxsec;
	const int MAX_DEPTH = 1000;

	int *core;
	ui *seq;

	ui *candStk; //size of candidate
	int endCand;	//position of last element
	int *depthCandStk; // The depth of the candidate stack in each depth
	int depth;
	#define START_CAND  (depthCandStk[depth-1])
	int *potentialCandStk;
	int *boundCandStk = nullptr;
	int *colorStk;
	int isoptimal;


	int *degreeInG;
	int *degreeOfCandidate;
	int	vtxOfMinDeg;
	int *rdegPlexStak;
	MBitSet64 PlexBitSet; // A bit set to keep all the growing vertices
	MBitSet64 satuBitSet;	// A bit set to keep all the growing saturated vertices;
	long long *scnt;
	long long *soldcnt;

	ui *PlexStk;
	int szPlex;

	clock_t startclk;
	clock_t endclk;
	uint64_t nnodes;
	
    ui *sol;
    ui szsol;

	typedef struct {
		MBitSet64 bitcolor;
		ui *vertices;
		int sz;
	}ColorType;
	ColorType *colors;
	int maxcolor;

    FastExactSearch(const MCsrGraph &csrg, int valueK, int maxsec, int lb=0){
		bg = new MBitGraph(csrg);
		rbg = new MBitGraph(csrg);
		rbg->reverseGraph();
		this->K = valueK;
		this->lb = lb;
		this->maxsec = maxsec;
		this->sol =  new ui[bg->nbvtx];
		this->szsol = lb;
		
		nnodes = 0;
		isoptimal = 1;
		//Init growing Plex
		PlexStk = new ui[bg->nbvtx];
		rdegPlexStak = new int[bg->nbvtx]; //|N(v)\cap Plex|
		szPlex = 0;


		candStk = new ui[bg->nbvtx*MAX_DEPTH];
		potentialCandStk = new int[bg->nbvtx*MAX_DEPTH];
		boundCandStk = new int[bg->nbvtx*MAX_DEPTH];
		endCand = 0;

		depth = 0;
		depthCandStk = new int[MAX_DEPTH + 1];
		depthCandStk[depth++] = 0;

		satuBitSet = MBitSet64(bg->nbvtx);	
		PlexBitSet = MBitSet64(bg->nbvtx);	
	//	tempSortCandStk = new ui[nbvtx];
		
		degreeInG = new int[bg->nbvtx];
		degreeOfCandidate = new int[bg->nbvtx];
		vtxOfMinDeg = -1;
		//Init candidate stack;
		int* core = new int[bg->nbvtx];
		ui* seq = new ui[bg->nbvtx];
		int* pos = new int[bg->nbvtx];
		//copy(vcore, vcore + bg->nbvtx, core);
		//copy(vseq, vseq + bg->nbvtx, seq);
		coreDecomposition(csrg, core, seq, pos);
		delete[] pos;
		for (int i = 0; i < bg->nbvtx; i++) {
			//push i into candidate by reversed degeneracy order.
			ui u = seq[bg->nbvtx - i - 1];
			candStk[endCand] = u;
			boundCandStk[endCand] = core[u] + K;
			//printf(" %d ", core[u] + K);
			++endCand;
			//notadjLst[u] = 0;
		}
		delete[] seq;

		//Init color order
	#if 0
		colorClass.resize(nbvtx+1);
		for (int i = 0; i < nbvtx + 1; i++)
			colorClass[i].clear();
	#endif
		//Init color
		colors = new ColorType[bg->nbvtx+1];
		for (int i = 0; i < bg->nbvtx + 1; i++) {
			colors[i].bitcolor = MBitSet64(bg->nbvtx);
			//colors[i].potential = new int[nbvtx];
			colors[i].vertices = new ui[bg->nbvtx];
			colors[i].sz = 0;
		}
		colorStk = new int[bg->nbvtx*MAX_DEPTH];
		
		scnt = new long long[bg->nbvtx];
		soldcnt = new long long[bg->nbvtx];
		memset(scnt, 0, sizeof(int)*bg->nbvtx);
		memset(soldcnt, 0, sizeof(int)*bg->nbvtx);

		//candSortByDescPortential();
	#ifdef DEBUG
		showStack();
	#endif
	}
	#define OP_BIT_THRESH(n) (n >> 6)
	inline int R_DEGREE(ui u) {return rbg->degree(u);}
	inline int DEGREE(ui u) {return bg->degree(u);}
	inline int intsecColor(ui u, int c) {
		return colors[c].bitcolor.intersect(*(bg->rows[u]));
	}
	void bitColorSort() {
		int j = 0; 
		maxcolor = 1;
		//int threshold = szSolution - szPlex;
		colors[1].sz = 0;
		colors[1].bitcolor.clear();
		colors[2].sz = 0;
		colors[2].bitcolor.clear();
		for (int i = START_CAND; i < endCand; i++) {
			int u = candStk[i];
			int c = 1;
			int sum = 0;
			while (1) {
				int con = intsecColor(u, c);
				//int con = countIntersection(mat[u], colors[c].bitcolor);
				if (con == 0) {
					break;
				}else
					c++;
			}
			colors[c].bitcolor.set(u);
			colors[c].vertices[colors[c].sz] = u;
			//colors[c].potential[colors[c].sz] = sum; //The number of neighbor vertices which can potentially form a k-plex with u; 
			colors[c].sz++;		
			//Open the next color to ensure correctness
			if (c > maxcolor) {
				maxcolor = c;
				colors[maxcolor + 1].bitcolor.clear();
				colors[maxcolor + 1].sz = 0;
			}
		}
		int start = START_CAND;
		int accbound = 0;
		for (int c = 1; c <= maxcolor; c++) {
			for (int i = 0; i < colors[c].sz; i++) {
				ui u = colors[c].vertices[i];
				candStk[start] = u;
				boundCandStk[start] = accbound + min(i + 1, K);
				colorStk[start] = c;
				potentialCandStk[start] = 0;
				if (boundCandStk[start] > szsol - szPlex){
					int itc = 1;
					while (itc < c) {
						potentialCandStk[start] += min(intsecColor(u, itc), K);
						itc++;
					}
				}
				start++;
			}
			accbound += min(colors[c].sz, K);
		}
		assert(start == endCand);
	}
	//int descentcmp(const void *a, const void *b)
	//{
	//	return degreeOfCandidate[*(int*)b] - degreeOfCandidate[*(int*)a];
	//}
	bool descentcmp(int a, int b){
		return degreeOfCandidate[a] > degreeOfCandidate[b];
	}
	struct CmpDescentCls {
		int* degree;
		CmpDescentCls(int* deg):degree(deg){}
		bool operator() (int i,int j) { return (degree[i]>degree[j]);}
	};

	void reorderCandAndComputeDeg() {
		int mindeg = bg->nbvtx;
		for (ui i = 0; i < szPlex; i++) {
			ui u1 = PlexStk[i];
			degreeInG[u1] = szPlex - rdegPlexStak[PlexStk[i]] - 1;
			for (int j = START_CAND; j < endCand; j++) {
				ui u2 = candStk[j];
				if ((bg->rows[u1])->test(u2)) {
					degreeInG[u1]++;				
				}
			}
			if (degreeInG[u1] < mindeg) {
				mindeg = degreeInG[u1];
				vtxOfMinDeg = u1;
			}
		}
		for (int i = START_CAND; i < endCand; i++) {
			int u1 = candStk[i];
			degreeInG[u1] = PlexBitSet.intersect(*(bg->rows[u1]));;
			degreeOfCandidate[u1] = 0;
			for (int j = START_CAND; j < endCand; j++) {
				if ((bg->rows[u1])->test(candStk[j])) {
					degreeOfCandidate[u1]++;
					degreeInG[u1]++;
				}
			}
			if (degreeInG[u1] < mindeg) {
				mindeg = degreeInG[u1];
				vtxOfMinDeg = u1;
			}
		}
		CmpDescentCls cmp(degreeOfCandidate);
		sort(candStk + START_CAND, candStk+endCand, cmp);
		//qsort(candStk + START_CAND, endCand - START_CAND, sizeof(ui), descentcmp);
	}
	void updateSaturateSet(ui u) {
		int szrnei = R_DEGREE(u);
		for (ui i = 0; i < szPlex - 1; i++) {
				ui rnei = PlexStk[i];
				if ((rbg->rows[u])->test(rnei)) {
					rdegPlexStak[rnei]++;
					rdegPlexStak[u]++;
					if (rdegPlexStak[rnei] == K - 1) {
						//we only keep vertices which newly become saturated vertices.
						satuBitSet.set(rnei);
					}
				}
				//printf("%d %d %d\n", rnei, rdegPlexStak[rnei], K-1);
				assert(rdegPlexStak[rnei] <= K - 1);
			}
		/*}*/
		if (rdegPlexStak[u] == K - 1) {
			satuBitSet.set(u);
		}
	}
	void intsecPlexInvNei(ui u, int *consat, int *cnt) {
		*cnt = 0;
		*consat = 0;
		if (szPlex < OP_BIT_THRESH(bg->nbvtx) ) { //i.e., nbvtx/32 
			for (int i = 0; i < szPlex; i++) {
				if ((rbg->rows[u])->test(PlexStk[i])) {
					(*cnt)++;
					if (satuBitSet.test(PlexStk[i])) {
						*consat = 1;
						*cnt = -1;
						break;
					}
				}
			}
		}
		else {
			*consat = satuBitSet.intersect(*(rbg->rows[u]));
			if (*consat == 0) {
				*cnt = PlexBitSet.intersect(*(rbg->rows[u]));
			}
			else {
				*cnt = -1; //Invalid
			}
			
		}
	}
	int interrupt() {
		if ((double)(clock() - startclk) / CLOCKS_PER_SEC > maxsec) {
			return 1;
		}
		//stop if the depth exceeds expectation.
		if (depth > MAX_DEPTH)
			return 2;
		return 0;
	}
	void deepen(ui u) {
		//We only consider the last candidate vertex under current config	
		PlexStk[szPlex] = u; // move to Plex
		PlexBitSet.set(u);
		rdegPlexStak[u] = 0;
		szPlex++;
		//update the best known
		if (szPlex > szsol) {
			copy(PlexStk, PlexStk + szPlex, sol);
			szsol = szPlex;
		}
	#ifdef DEBUG
		if (endPlex == 5 && u == 2)
			printf("pause\n");
	#endif
		//Update the saturated vertices in the growing Plex
		updateSaturateSet(u);
		
		//Update candidate. The ones which are adjacent to saturated vertices will be removed
		int savePtrCand = endCand; 	
		for (int ptr = START_CAND; ptr < savePtrCand; ptr++) {
			ui cand = candStk[ptr];
			//TODO: we can optimize the counter.
			int notadj, consatu;
			intsecPlexInvNei(cand,  &consatu, &notadj);
			if (consatu == 0 && notadj <= K-1){
				candStk[endCand] = cand;
				//if (!sw_colorsort)
				//	boundCandStk[endCand] = boundCandStk[ptr];	// the bound is reinitialized in color sort.
				endCand++;
			}				
		}
		depthCandStk[depth++] = savePtrCand;
	}
	void bracktrack() {
		ui u = PlexStk[szPlex-1]; // pop a vertex u from plex stk
		
		//update saturate set
		assert(rdegPlexStak[u] < K);
		if (rdegPlexStak[u] == K - 1) { //u is a saturated vertex
			assert(satuBitSet.test(u));
			satuBitSet.set(u);//cancel u as a saturated vertex
		}
		for (int i = 0; i < szPlex-1; i++) {
			ui rnei = PlexStk[i];
			if ((rbg->rows[u])->test(rnei)){			
				rdegPlexStak[rnei]--;			
				if (rdegPlexStak[rnei] == K - 2) {
					//we only keep vertices which newly become saturated vertices.
					assert(satuBitSet.test(rnei));
					satuBitSet.set(rnei);
				}
				rdegPlexStak[u]--;
			}
		}
		assert(rdegPlexStak[u] == 0);		
		szPlex--; //Drop the vertex
		PlexBitSet.set(u);

		//rewind
		endCand = depthCandStk[--depth];	
	}

	#ifdef DEBUG
	void showStack() {
		printf("-Depth- %d\n", depth);
		printf("Plex: ");
		for (int i = 0; i < endPlex; i++) {
			printf("%d ", PlexStk[i]);
		}
		printf("\nCand: ");
		for (ui i = startCand; i < endCand; i++) {
			printf("%d ", candStk[i]);
		}
		printf("\n");

	}
	#else
	void showStack() {}
	#endif

	void expand() {
		//int stop = 0;
		nnodes++;
		scnt[szPlex + 1] = scnt[szPlex + 1] + scnt[szPlex] - soldcnt[szPlex + 1];
		soldcnt[szPlex + 1] = scnt[szPlex];
		if (szPlex + (endCand - START_CAND) <= szsol)
			return;
		
		/*if ((double)scnt[szPlex + 1] / nbranch < tlimit) {
			reorderCandAndComputeDeg();
			if (degreeInG[vtxOfMinDeg] >= szPlex + (endCand - START_CAND) - K) {
				copy(PlexStk, PlexStk + szPlex, solution);
				szSolution = szPlex;
				copy(candStk + START_CAND, candStk + endCand, solution + szSolution);
				szSolution += (endCand - START_CAND);
				return;
			}
		}*/
		bitColorSort();
		//TODO: add dominance to the algorithm. i.e., if N(u)\subset N(v): then, delete[v]-> delete[u]
		//How to compute dominance: triangle counting.
		while (endCand-START_CAND > 0) {
			if (interrupt()) { //stop due to interruption
				isoptimal = 0;
				break;
			}
			
			if (szPlex + boundCandStk[endCand - 1] <= szsol || szPlex + (endCand - START_CAND) <= szsol) {
				return;
			}
			
			if (szPlex + potentialCandStk[endCand-1] + K <= szsol ) {
				endCand--; //pop stack and continue
				continue;
			}

			ui u = candStk[endCand - 1];
			endCand--; // Pop u from cand stack			

			//update Plex
	#ifdef DEBUG
			printf("--------------Take %d and deepen ---------------\n", u);
	#endif
			deepen(u);
	#ifdef DEBUG
			showStack();
	#endif			
			expand();
			bracktrack();					
		}
		
	}

    void search(){
		startclk = clock();
		//start to search the optimal solution.
		expand(); 
		endclk = clock();
	}

    double getRunningTime(){
		return Utility::elapse_seconds(startclk, endclk);
	}
	uint64_t getRunningNodes(){
		return nnodes;
	}
    void getBestSolution(ui *vtx, ui &sz){
		sz = szsol;
		memcpy(vtx, sol, sizeof(ui) * szsol);
	}
	
};


