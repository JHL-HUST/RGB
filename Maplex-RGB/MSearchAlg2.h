#pragma once
#include <algorithm>
#include <assert.h>
#include "MGraph.h"
#include "LinearHeap.h"
using namespace std;

class FastExactSearch2{
public:
	const MCsrGraph &cg;
    MBitGraph *bg;
	MBitGraph *rbg;
    int K;
    int lb;
	int maxsec;
	int *core;
	ui *seq;
	int* triangles;

	ui* stkvtx;
	int* stkcon2p;
	int* stkbound;
	int* stkpcolor;
  
  int* stkclevel;
  int* stkpoint_color;
  
  int** clevel;
  int** point_color;
  //int* index;
  
	int** con2p; 
	int** bound;
	int** pcolors;
   
  ui **nbnn;
  ui **nbnn2;
   
	int *plexpos;
	int *candpos;
	int depth;

	clock_t startclk;
	clock_t endclk;
	uint64_t nnodes;
	
	int ub;
    ui *sol;
    int szsol;
	int isoptimal;

	typedef struct {
		MBitSet64 bitcolor;
		ui *vertices;
		int sz;
    //int level;
    //int orgsz;
	}ColorType;
	ColorType *colors;
	int* maxcolor;
#define PLSTART(d)	(plexpos[d])
#define PLEND(d)	(candpos[d])
#define CASTART(d) (candpos[d])
#define CAEND(d)	(plexpos[d+1])	
#define SZ_PLEX(d) (PLEND(d) - PLSTART(d))	//number of vertices in P
#define SZ_CAND(d)	(CAEND(d) - CASTART(d)) //number of vertices in C
#define SZ_VTX(d) (CAEND(d) - PLSTART(d)) // number of verices in P union C

    FastExactSearch2(const MCsrGraph &csrg, int valueK, int maxsec, int lb=0):
	cg(csrg){
    
    //printf("%d %d\n",csrg.nbedges, csrg.nbvtx);
    //for (int ii = 0; ii < csrg.nbedges; ii++){
    //  if (csrg.edges[ii] == 0)
    //    printf("!!!!!!!!\n");
    //}
    /*
    for (int ii = 0; ii < csrg.nbvtx; ii++)
      printf("%d ",csrg.pstart[ii]);
    printf("\n\n");
    for (int ii = 0; ii < csrg.nbedges; ii++)
      printf("%d ",csrg.edges[ii]);
    printf("\n");
    */
		bg = new MBitGraph(csrg);
		rbg = new MBitGraph(csrg);
		rbg->reverseGraph();
		this->K = valueK;
		this->lb = lb;
		this->maxsec = maxsec;
		this->nnodes = 0UL;
		this->sol =  new ui[bg->nbvtx];
		this->szsol = lb;		
		//cout << lb <<endl;

		//Initialize bound
		core = new int[bg->nbvtx];
		seq = new ui[bg->nbvtx];
    
    maxcolor = new int[bg->nbvtx];
    //clevel = new int[bg->nbvtx];
    //point_color = new int[bg->nbvtx];
    //index = new int[bg->nbvtx];
    
    nbnn = new ui*[K];
    nbnn2 = new ui*[K];
    
    for (int i = 0; i < K; i++){
      nbnn[i] = new ui[bg->nbvtx];
      nbnn2[i] = new ui[bg->nbvtx];
    }
    
		int* vpos = new int[bg->nbvtx];
		//triangles = new int[cg.nbedges];
		int maxcore = coreDecomposition(cg, core, seq, vpos);
		//countingTriangles(cg, vpos, triangles);
		delete[] vpos;
		
		ub =  maxcore+K + 1;
		nnodes = 0;
		isoptimal = 1;

		stkvtx = new ui[csrg.nbvtx * ub];
		stkcon2p = new int[csrg.nbvtx * ub];
		stkbound = new int[csrg.nbvtx * ub];
		stkpcolor = new int[(csrg.nbvtx + 1) * ub];
		stkclevel = new int[(csrg.nbvtx + 1) * ub];
    stkpoint_color = new int[(csrg.nbvtx + 1) * ub];
    
		con2p = new int*[ub];
		bound = new int*[ub];
		pcolors = new int*[ub];
    clevel = new int*[ub];
    point_color = new int*[ub];
		for (int d = 0; d < ub; d++) {
			con2p[d] = &(stkcon2p[csrg.nbvtx * d]);
			bound[d] = &(stkbound[csrg.nbvtx * d]);
			pcolors[d] = &(stkpcolor[(csrg.nbvtx + 1) * d]);
      clevel[d] = &(stkclevel[(csrg.nbvtx + 1) * d]);
      point_color[d] = &(stkpoint_color[(csrg.nbvtx + 1) * d]);
		}
    
		plexpos = new int[ub + 1];
		candpos = new int[ub + 1];
		//Init color
		colors = new ColorType[bg->nbvtx+1];
		for (int i = 0; i < bg->nbvtx + 1; i++) {
			colors[i].bitcolor = MBitSet64(bg->nbvtx);
			colors[i].vertices = new ui[bg->nbvtx];
			colors[i].sz = 0;			
		}			
   
		pcolors[0][0] = 0;
		
		depth = 0;
		PLSTART(depth) = 0;
		PLEND(depth) = 0;
		CASTART(depth) = 0;
		int pos = CASTART(depth);
		for (int i = 0; i < bg->nbvtx; i++) {
			ui u = seq[bg->nbvtx - i - 1];		
			stkvtx[pos++] = u;
			bound[depth][u] = core[u] + K;
			//potent[depth][u] = core[u];
			con2p[depth][u] = 0;			
		}
		CAEND(depth) = pos;
		PLSTART(depth+1) = CAEND(depth);
		

		//candSortByDescPortential();
		#ifdef DEBUG
			showStack();
		#endif
	}

	#define OP_BIT_THRESH(n) (n >> 6)
	inline int intsecColor(ui u, int c) {
		return colors[c].bitcolor.intersect(*(bg->rows[u]));
	}
  
  void bitColorSort2() {
    maxcolor[depth] = 1;
    int c;
    int acccolor = 0;
		int nbnn_num[K], nbnn_num2[K];
    for (int i = 0; i < K; i++) {
			nbnn_num[i] = 0;
		}
		for (int i = CASTART(depth); i < CAEND(depth); i++) {
			ui v = stkvtx[i];
			int uncon_num = SZ_PLEX(depth)-con2p[depth][v];
      nbnn2[uncon_num][nbnn_num[uncon_num]] = v;
			nbnn[uncon_num][nbnn_num[uncon_num]++] = v;
		}
    for (int i = 0; i < K; i++) {
			nbnn_num2[i] = nbnn_num[i];
		}
    for (int i = K-1; i >= 0; i--) {
      if (nbnn_num[i] == 0) continue;
      colors[acccolor+1].sz = 0;
		  colors[acccolor+1].bitcolor.clear();
		  colors[acccolor+2].sz = 0;
		  colors[acccolor+2].bitcolor.clear();
      for (int j=0; j<nbnn_num[i]; j++) {
				int u = nbnn[i][j];
				c = acccolor+1;
				while (1) {
					int con = intsecColor(u, c);
					if (con == 0) {
						break;
					}else
						c++;
				}
				colors[c].bitcolor.set(u);
				colors[c].vertices[colors[c].sz] = u;
        point_color[depth][u] = c;
				colors[c].sz++;		
				if (c > maxcolor[depth]) {
					maxcolor[depth] = c;
					colors[maxcolor[depth] + 1].bitcolor.clear();
					colors[maxcolor[depth] + 1].sz = 0;
				}
			}
      for (int j = acccolor+1; j <= maxcolor[depth]; j++){
        clevel[depth][j] = i;
      }
      for (int j = acccolor+1; j <= maxcolor[depth]; j++) {
				int insert[K-i];
				int insert_num = 0;
				for (int t = 0; t < i; t++) {
					if (nbnn_num[t] == 0) continue;
          for (int l=0; l<nbnn_num[t]; l++) {
						ui v = nbnn[t][l];
						int con = intsecColor(v, j);
						if (con == 0) {
							insert[insert_num++] = v;
							nbnn[t][l] = nbnn[t][nbnn_num[t]-1];
							nbnn_num[t]--;
							l--;
							if (insert_num == K-i) {
								break;
							}
						}
					}
					if (insert_num == K-i) {
						break;
					}
        }
        if (insert_num > 0){
          for (int t = 0; t < insert_num; t++){
            colors[j].bitcolor.set(insert[t]);
    				colors[j].vertices[colors[j].sz] = insert[t];
            point_color[depth][insert[t]] = j;
    				colors[j].sz++;	
          }
        }
      }
      acccolor = maxcolor[depth];
    }
    
    int color_num[maxcolor[depth]+1];
    for (int i = 1; i <= maxcolor[depth]; i++)
      color_num[i] = 0;
    int pos = CASTART(depth);
    int accbound = 0;
    for (int i = 0; i < K; i++){
      if (nbnn_num2[i] == 0)  continue;
      for (int j = 0; j < nbnn_num2[i]; j++){
        ui u = nbnn2[i][j];
        stkvtx[pos++] = u;
        color_num[point_color[depth][u]]++;
        if (color_num[point_color[depth][u]] <= K - clevel[depth][point_color[depth][u]])
          bound[depth][u] = ++accbound;
        else
          bound[depth][u] = accbound;
      }
    }
  }
  
	void showcolor(int vpos){
		printf("vertex: %d\n", stkvtx[vpos]);
		printf("Pos: \n" );
		for (int i = CASTART(depth); i < vpos; i++){
			printf("%d\t",i);
		}
		printf("cand [%d]: \n", vpos - CASTART(depth));
		for (int i = CASTART(depth); i < vpos; i++){
			printf("%d\t",stkvtx[i]);
		}
		printf("\n");
		printf("connection: \n");
		for (int i = CASTART(depth);i < vpos; i++){
			if (bg->rows[stkvtx[vpos]]->test(stkvtx[i]))
				printf("1\t");
			else printf("0\t");
		}
		printf("\n");
		printf("colors start: %d ", CASTART(depth));
		for (int c = 1; pcolors[depth][c] != cg.nbvtx + 1; c++){
			printf("C%d: %d | ", c, pcolors[depth][c]);
		}
		printf("\n");

	}
 
  int lookahead2(int vpos){
    int sum = 0;
    int intesec_num[maxcolor[depth]];
    for (int i = 1; i <= maxcolor[depth]; i++)
      intesec_num[i] = 0;
    for (int i = CASTART(depth); i < vpos; i++){
      if (bg->rows[stkvtx[vpos]]->test(stkvtx[i])){
        int c = point_color[depth][stkvtx[i]];
        intesec_num[c]++;
      }
    }
    for (int i = 1; i <= maxcolor[depth]; i++)
      sum += min(intesec_num[i], K-clevel[depth][i]);
    
    return sum;
  }
  
	int interrupt() {
		if ((double)(clock() - startclk) / CLOCKS_PER_SEC > maxsec) {
			return 1;
		}
		return 0;
	}

	void refineCandidate(){
		if (SZ_PLEX(depth) == 0) return;
		MBitSet64 mask(cg.nbvtx);
		for (int i = PLSTART(depth); i < CAEND(depth); i++){
			mask.set(stkvtx[i]);
		}
		ui lastu = stkvtx[PLEND(depth)-1];
		mask &= *(bg->rows[lastu]);
		int pos = CASTART(depth);
		
		for (int i = CASTART(depth); i < CAEND(depth); i++){
			ui v = stkvtx[i];
			int com = bg->rows[v]->intersect(mask);
			if (mask.test(v) && com + 2* K > szsol){
				stkvtx[pos++] = v; // keep v
			}else if (!mask.test(v) && com + 2*K -2 > szsol){
				stkvtx[pos++] = v; //keep v
			}else{
				if (mask.test(v)) mask.set(v);				
			}
		}
		CAEND(depth) = pos;
	}

	/** 
	 * move the last vertex in stkcand to plex
	 * increase the stack level
	 * update stkvtx, stkcon2p, stkdeg.
	 * */
	void selectLast() {
		//We only consider the last candidate vertex under current config	
		ui u = stkvtx[CAEND(depth) - 1];
		MBitSet64 gmark(cg.nbvtx);		
		//update the best known		
		set<ui> satu;
		int pos = PLSTART(depth+1);		
	#ifdef DEBUG
		printf("--------------Take %d and deepen ---------------\n", u);
	#endif
		//Update the saturated vertices in the growing Plex
		//stkcon2p[depth+1] = stkcon2p[depth]; 
		for (ui i = PLSTART(depth); i < PLEND(depth); i++){
			ui v = stkvtx[i];
			int con = con2p[depth][v];
			if (bg->rows[v]->test(u)){
				con++;
			}			
			if (con == depth + 1 - K){
				satu.insert(v); // satu vertex
			}
			con2p[depth+1][v] = con;
			stkvtx[pos++] = v;			
			gmark.set(v);
		}
		if (con2p[depth][u] == depth + 1 - K)
			satu.insert(u);
		stkvtx[pos++] = u;		
		//gmark.set(u);
		con2p[depth+1][u] = con2p[depth][u];
		
		PLSTART(depth + 1) = CAEND(depth);
		PLEND(depth + 1) =  pos;
		assert(depth + 1 == SZ_PLEX(depth+1));
		assert(CASTART(depth + 1) == PLEND(depth+1));

		//check every candidate vertex except the last one.
		for (int i = CASTART(depth); i < CAEND(depth) - 1; i++){
			ui v = stkvtx[i];
			int kept = 1;
			int con = con2p[depth][v];
			//check if v is kept in the new solution			
			for (auto x: satu){
				//x is not connected to v, remove
				if (!bg->rows[x]->test(v)){
					kept = 0;
					break;
				}
			}			
			if (kept){				
				if (bg->rows[v]->test(u)){
					con++;
				}
				if (con + K < depth + 2){
					kept = 0;
				}
			}

			if (kept){
				//push into stack without changing the order
				con2p[depth+1][v] = con;
				stkvtx[pos++] = v;				
			}
		}
		CAEND(depth+1) = pos;
	}
	

#ifdef DEBUG
	void showStack() {
		printf("depth: %d\n", depth);
		printf("PLEX SZ %d : ", SZ_PLEX(depth));
		for (int i = PLSTART(depth); i < PLEND(depth); i++){
			int v = stkvtx[i];
			printf("%d(toP:%d, deg%d)\n  ", v, stkcon2p[i], stkdeg[i][v]);
		}
		printf("\n CAND SZ %d: ", SZ_CAND(depth));
		for (int i = CASTART(depth); i < CAEND(depth); i++){
			ui v = stkvtx[i];
			printf("%d(toP: %d, deg%d)\n ", v, stkcon2p[i], stkdeg[depth][stkvtx[i]]);
		}
		printf("\n");
	}
	#else
	void showStack() {}
	#endif
	void checkDegree(){
		int *deg = new int[cg.nbvtx];
		for (int i = PLSTART(depth); i < CAEND(depth); i++){
			ui u = stkvtx[i];
			deg[u] = 0;
			for (int j = PLSTART(depth); j < CAEND(depth); j++){
				ui v = stkvtx[j];
				if (bg->rows[u]->test(v)){
					deg[u]++;
				}
			}
			//assert(deg[u] == stkdeg[depth][u]);
		}		
	}

	void expand() {
		//int stop = 0;
		nnodes++;
		assert(depth == SZ_PLEX(depth));
		//checkDegree();
		if (SZ_PLEX(depth) > szsol){
			copy(stkvtx + PLSTART(depth), stkvtx + PLEND(depth), sol);
			szsol = SZ_PLEX(depth);
		}		
	#ifdef DEBUG
			showStack();
	#endif		
		if (SZ_VTX(depth) <= szsol)
			return;
		refineCandidate();
		if (SZ_VTX(depth) <= szsol)
			return;
    bitColorSort2();
		while (SZ_CAND(depth) > 0) {
			if (interrupt()) { //stop due to interruption
				isoptimal = 0;
				break;
			}
			ui last = stkvtx[CAEND(depth) - 1];
			if (SZ_PLEX(depth) + bound[depth][last] <= szsol || SZ_PLEX(depth) + SZ_CAND(depth) <= szsol) {
				return;
			}
			/*  color bound*/			
			int tol = K - SZ_PLEX(depth) + con2p[depth][last];
			int potential = lookahead2(CAEND(depth) - 1);
			if (SZ_PLEX(depth) + potential + tol <= szsol ) {		
				--CAEND(depth);
				continue;
			}

			//update Plex
			selectLast();			
			++depth;		
			
			expand();
			
			//drop the last vertex
			--depth;	
			--CAEND(depth);
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





class FastHeuSearch{
public:
	MCsrGraph &g;
	int K;
	int *core;
	int issort;
	ui *seq;
	int *pos;
	
	ui* sol;
	int szsol;
	
	ui* curP;
	int szP;
	int* degP;
	const int maxdepth = 1;

	FastHeuSearch(MCsrGraph &csrg, int valueK):	g(csrg), K(valueK){
		core = new int[g.nbvtx];
		seq = new ui[g.nbvtx];
		pos = new int[g.nbvtx];
		szsol = 0;
		sol = new ui[g.nbvtx];
    //point_color = new int[g.nbvtx];
		issort= 0;
	}

	~FastHeuSearch(){
		delete[] core;
		delete[] seq;
		delete[] pos;
		delete[] sol;
    //delete[] clevel;
    //delete[] point_color;
 	}

	void Add2P(ui u){
		for (ui j = g.pstart[u]; j < g.pstart[u+1]; j++){
			ui nei = g.edges[j];
			degP[nei]++;
		}
	}
	void DelFrP(ui u){
		for (ui j = g.pstart[u]; j < g.pstart[u+1]; j++){
			ui nei = g.edges[j];
			degP[nei]--;
		}
	}
	int isFeasible(ui u){
		if (degP[u] + K < szP + 1)	return 0;
		int isf = 1;
		for (int i = 0; i < szP; i++){
			int v = curP[i];
			if (degP[v] == szP - K){ //satu
				ui *it = find(g.edges+ g.pstart[u], g.edges+g.pstart[u+1], v);
				if (it == g.edges + g.pstart[u+1]){
					isf = 0;
					break;
				}
			}
		}
		return isf;
	}
	void expand(ui* cand, ui szc){
		while(szc > 0){
			if (szP + szc <= szsol || szP + core[cand[szc-1]] + K <= szsol){ 
				break;
			}
			ui u = cand[--szc];//pop u
			curP[szP++] = u;
			Add2P(u);
			ui tsz = szc;
			szc = 0;
			for (int j = 0; j < tsz; j++){
				if (isFeasible(cand[j])){
					cand[szc++] = cand[j];
				}
			}
			if (szP > szsol){
				szsol = szP;
				memcpy(sol, curP, szsol * sizeof(ui));
			}
		}
	}

	void heuPolish(){
		if (!issort){
			coreDecomposition(g, core, seq, pos);
			issort = 1;
		} 
		curP = new ui[g.nbvtx];
		szP = 0;
		degP = new int[g.nbvtx];
		
		
		ui *cand = new ui[g.nbvtx];
		ui szc = 0;
		
		for (int i = 0; i < g.nbvtx; i++){
			ui u = seq[g.nbvtx - i -1];
			if (core[u] + K <= szsol) break;
			curP[0] = u;
			szP = 1;
			szc = g.nbvtx - i - 1;	
			memcpy(cand, seq, sizeof(ui) * szc);		
			memset(degP, 0, sizeof(int) * g.nbvtx);
			for (ui j = g.pstart[u]; j < g.pstart[u+1]; j++)
				degP[g.edges[j]] = 1; 
			expand(cand, szc);			

			szP = 0;
		}
		delete[] cand;
		printf("The maximum solution after polish %d\n", szsol);
	}
	void coreHeurSolution(){    
		assert(core != nullptr && seq != nullptr && pos != nullptr && sol != nullptr);

		int *deg = new int[g.nbvtx];
		szsol = 0;
		MBitSet64 *issol = new MBitSet64(g.nbvtx);
		int maxcore = -1;
		int hit = 0;

		for (ui i = 0; i < g.nbvtx; i++) {		
			deg[i] = g.degree(i);
			seq[i] = i;
			core[i] = -1;
		}
		ListLinearHeap *linear_heap = new ListLinearHeap(g.nbvtx, g.nbvtx);
		linear_heap->init(g.nbvtx, g.nbvtx - 1, seq, (ui*)deg);
		for (ui i = 0; i < g.nbvtx; i++) {
			ui u, key;
			linear_heap->pop_min(u, key);
			if ((int)key > maxcore) 
				maxcore = key;		
			seq[i] = u;
			core[u] = maxcore;
			pos[u] = i;
			if (key >= g.nbvtx-i -K && !hit){
				ui sz = i+1;			
				linear_heap->get_ids_of_larger_keys(seq, sz, key);							
				for (ui j = i+1; j < g.nbvtx; j++){//vertices after i is not ordered
					//core[seq[j]] = max_core;				
					sol[szsol++] = seq[j];				
					issol->set(seq[j]);
				}
				hit = 1;
				//break;
			}
		
			for (ui j = g.pstart[u]; j < g.pstart[u + 1]; j++){
				if (core[g.edges[j]] == -1)
					linear_heap->decrement(g.edges[j]);
			}
		}	
		issort = 1;
		//extend the heuristic solution.
		//compute degrees
		memset(deg, 0, sizeof(int) * g.nbvtx);	
		//MBitSet64 *issatu = new MBitSet64(og_nbvtx);
		int nsatu = 0;
		for (int i = 0; i < szsol; i++){
			ui u = sol[i];
			//printf("%d ", u);
			for (ui j = g.pstart[u]; j < g.pstart[u+1]; j++){
				ui nei = g.edges[j];
				if (issol->test(nei)){
					deg[u]++;
				}
			}
			if (deg[u] == szsol - K){
				nsatu ++;
			}
		}
		//extending the remaining vertices
		for (int i = g.nbvtx - szsol - 1; i >= 0; i--){
			ui u = seq[i];
			if (core[u] + K <= szsol) break;
			int cntnei = 0, cntsatu = 0;
			for (int j = g.pstart[u]; j < g.pstart[u+1]; j++){
				ui nei = g.edges[j];
				if (issol->test(nei)){
					cntnei++;
					if (deg[nei] == szsol - K){ //nei is satu
						cntsatu++;
					}
				}			
			}
			//extend u
			if (cntnei >= szsol - K + 1 && cntsatu == nsatu){ 
				printf("extend %d\n",u);
				assert(deg[u] == 0);
				deg[u] = cntnei;
				sol[szsol++] = u;			
				issol->set(u);
				//update number of saturated vertices.			
				for (ui j = g.pstart[u]; j < g.pstart[u+1]; j++){
					ui nei = g.edges[j];
					if (issol->test(nei)){
						deg[nei]++;
					}
				}
				//recount satu vertices
				nsatu = 0;
				for (int j = 0; j < szsol; j++){				
					if (deg[sol[j]] == szsol - K){
						nsatu++;
					}
				}
			}
		}
		
		delete linear_heap;
		delete issol;
		delete[] deg;
		printf("The maximum heuristc solution %d\n", szsol);

	}	
};



