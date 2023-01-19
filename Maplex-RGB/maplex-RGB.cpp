#include <stdio.h>
#include <algorithm>
#include "LinearHeap.h"
#include "MGraph.h"
#include "MBitSet.h"
#include "MSearchAlg2.h"
#ifdef NDEBUG
#undef NDEBUG
#include <assert.h>
#endif

//char filename[1024] = "instances\\hamming6-2.bin";
//char filename[1024] = "social-nework\\kernal\\memplus.bin.ker";
char filename[1024] = "realinstances\\binfmt\\ca-hollywood-2009.bin";
//char filename[1024] = "instances\\johnson8-4-4.bin";
int paraK = 2;
int paraReductLevel = 2;//0:no reduct. 1: core reducet 2:2nd lv reduct
int maxsec = 1000;

/*return 1 if set in vtx is a k-plex in graph csrg*/
int verifyKplex(MCsrGraph &csrg, int valuek, ui* vtx, ui sz){
    int nbvtx = csrg.nbvtx;
    int *deg = new int[nbvtx];
	MBitSet64* issol = new MBitSet64(nbvtx);
	memset(deg, 0, sizeof(int) * nbvtx);
	for (int i = 0; i < sz; i++)
		issol->set(vtx[i]);

	for (int i = 0; i < sz; i++){
		int u = vtx[i];
		for (int j = csrg.pstart[u]; j < csrg.pstart[u+1]; j++){
			int nei = csrg.edges[j];
			if(issol->test(nei)){
				deg[u]++;
			}
		}
	}
	int iskplex = 1;
	for (int i = 0; i < sz; i++){
		if (deg[vtx[i]] < sz - valuek){
			iskplex = 0;
			break;
		}

	}
	delete[] deg;
	return iskplex;
}

/*Build a subgraph from g*/


void induceSubgraph(const MCsrGraph &g, MCsrGraph &subg, ui* vtxlst, int sz, map<ui,ui> &idtbl, int lb){
	if(sz <= lb) {
		sz = 0;
	}
	ui *gid2sub = new ui[g.nbvtx];	//gid2sub[i], vertex i in g is vertex gidsub[i] in subg
	ui *sub2gid = new ui[sz];		//sub2gid[j], vertex j in subg is vertex sub2gid[j] in g;
    assert(gid2sub != nullptr && sub2gid != nullptr);

    subg.nbvtx = sz;
    subg.pstart = new int[subg.nbvtx+1];
    subg.nbedges = 0;
    subg.pstart[0] = 0;
    
    ui *tedges = new ui[g.nbedges];
    MBitSet64 mark(g.nbvtx);
    for (int i = 0; i < sz;i++){
        assert(vtxlst[i] >= 0 &&vtxlst[i] < g.nbvtx);
        assert(!(mark.test(vtxlst[i])));  
        mark.set(vtxlst[i]);
        gid2sub[vtxlst[i]] = i;
        sub2gid[i] = vtxlst[i];
		idtbl[i] = vtxlst[i];            
    } 

    for (int i = 0; i < sz; i++){
        int u = vtxlst[i];
        subg.pstart[i+1] = subg.pstart[i];	
        for (int j = g.pstart[u]; j < g.pstart[u+1]; j++){
            ui nei = g.edges[j];
            if (mark.test(nei)){
                tedges[subg.pstart[i+1]++] = gid2sub[nei]; 
                subg.nbedges++;
            }
        } 
    } 
    assert(subg.nbedges == subg.pstart[sz]);
    subg.edges = new ui[subg.nbedges];
    memcpy(subg.edges, tedges, sizeof(ui) * subg.nbedges);
    delete[] tedges;
    delete[] gid2sub;
	delete[] sub2gid;
    //printf("Reduced size %d, %d\n", subg.nbvtx, subg.nbedges);   
}



//The number of vertices will not change
int *cg_pstart;
int *cg_pend;
ui *cg_edges; //unordered
int *cg_valid;
int cg_nbvtx;
int cg_nbedges;
int cg_maxvtx;
int cg_maxedge;
int cg_MAXNBEDGES;
//TODO:keep vertice 
map<ui, vector<ui> > cg_vmp;

int cg_setIntersection(ui* first1, ui* last1, ui* first2, ui* last2){
	vector<ui> v(last1 - first1);
	auto it = set_intersection(first1, last1, first2, last2, v.begin());
	return (int)(it - v.begin());
}

inline int cg_deg(ui u){
	return cg_pend[u] - cg_pstart[u];
}

/** Counting triangles for each edge cg_edge[j], j=cg_pstart[u] + i
 *  traingle[j] is avalaible only if u < cg_edges[j];
 */
void cg_countingTriangles(int *triangles){
	 //triangle counting
	assert(triangles != nullptr);
	//counting triangles
	//memset(triangles, -1, sizeof(int) * cg_maxedge);
	for (ui u = 0; u < cg_maxvtx; u++){
		if (cg_valid[u]){
			for (int j = cg_pstart[u]; j < cg_pend[u]; j++){
				ui neiu = cg_edges[j];				
				if (u < neiu){
					//triangles[j] = cg_setIntersection(cg_edges + cg_pstart[u], cg_edges + cg_pend[u],
					//cg_edges + cg_pstart[neiu], cg_edges + cg_pend[neiu]);
					triangles[j] = countIntersect(cg_edges + cg_pstart[u], cg_deg(u),
					cg_edges + cg_pstart[neiu], cg_deg(neiu));
					//countIntersect(g.edges+g.pstart[u], g.degree(u), g.edges+g.pstart[neiu], g.degree(neiu));
				}
			}
		}
	}
}

/** Remove vertex u from cg graph.
 * ensure the neighbors of u are sorted in ascending order.
 * */
void cg_removeVtx(ui u){
	assert(cg_valid[u] && u < cg_maxvtx);
	for (int i = cg_pstart[u]; i < cg_pend[u]; i++){
		ui neiu = cg_edges[i];
		//Find u from neighbors of neiu.
		int posu = distance(cg_edges, find(cg_edges + cg_pstart[neiu], cg_edges + cg_pend[neiu], u));	
		//remove u from N(neiu)
		for (ui p = posu; p < cg_pend[neiu] - 1; p++) cg_edges[p] = cg_edges[p+1];
		cg_pend[neiu]--;		
	}
	cg_nbedges -= 2*(cg_pend[u] - cg_pstart[u]);
	cg_valid[u] = 0;	//mark u as removed
	cg_nbvtx--;
	cg_pend[u] = cg_pstart[u]; //TODO:remove
}

/** Remove edge (u, v) from cg
 */
void cg_removeEdge(ui u, ui v){
	assert(cg_valid[u] && cg_valid[v]);
	int posv = distance(cg_edges, find(cg_edges + cg_pstart[u], cg_edges + cg_pend[u], v));
	for (int p = posv; p < cg_pend[u] - 1; p++) cg_edges[p] = cg_edges[p+1];
	cg_pend[u]--;

	int posu = distance(cg_edges, find(cg_edges + cg_pstart[v], cg_edges + cg_pend[v], u));
	for (int p = posu; p < cg_pend[v] - 1; p++) cg_edges[p] = cg_edges[p+1];	
	cg_pend[v]--;

	cg_nbedges -= 2;
}
/*
* remove edge cg_edges[e] from cg. 
* e locates in cg_pstart[u] to cg_pend[u].
*/
void cg_removeEdge(ui u, int e){
	assert(cg_valid[u]);	
	assert(e >= cg_pstart[u] && e < cg_pend[u]);
	assert(cg_valid[cg_edges[e]]);
	ui v = cg_edges[e];
	int posu = distance(cg_edges, find(cg_edges + cg_pstart[v], cg_edges + cg_pend[v], u));
	for (int p = posu; p < cg_pend[v] - 1; p++) cg_edges[p] = cg_edges[p+1];	
	cg_pend[v]--;

	for (int p = e; p < cg_pend[u] - 1; p++) cg_edges[p] = cg_edges[p+1];
	cg_pend[u]--;

	cg_nbedges -= 2;
}


/** 
 * merge two vertices u and v.
 * the index of new vertex u' is still u. 
 * But the neigbors of new vertex u' is the union of N(u) and N(v)
 */
ui cg_mergeVtx(ui u, ui v){
	assert(cg_valid[u] && cg_valid[v]);
	//create a new vertex w with id cg_nbvtx;
	ui w = cg_maxvtx;
	int ecnt = 0;
	cg_pstart[w] = cg_maxedge;
	cg_pend[w] = cg_maxedge;
	set<ui> neiset;
	for (ui i = cg_pstart[u]; i < cg_pend[u]; i++)	neiset.insert(cg_edges[i]);	
	for (ui i = cg_pstart[v]; i < cg_pend[v]; i++)	neiset.insert(cg_edges[i]);	
	if(neiset.find(v) != neiset.end()){
		neiset.erase(v); neiset.erase(u);
	}
	if (cg_maxedge >= cg_MAXNBEDGES) {fprintf(stderr, "CG MEMOERY ERROR\n");}
	for (auto x: neiset) cg_edges[cg_pend[w]++] = x;	//printf("%d ",x);	}//printf("\n");
	cg_maxedge += neiset.size();	
	ecnt += neiset.size();

	for (ui i = cg_pstart[w]; i < cg_pend[w]; i++){
		ui x = cg_edges[i];
		int idu = distance(cg_edges, bsearch_with_index(cg_edges + cg_pstart[x], cg_edges + cg_pend[x], u));
		int idv = distance(cg_edges, bsearch_with_index(cg_edges + cg_pstart[x], cg_edges + cg_pend[x], v));
		int inval = cg_pend[x];
		if (idu != inval && idv != inval){
			//remove v
			for (int p = idv; p < cg_pend[x] - 1; p++) cg_edges[p] = cg_edges[p+1];
			--cg_pend[x];
			--ecnt;
		}else if (idu != inval && idv == inval){
			//keep unchanged
		}else if (idu == inval && idv != inval){
			//change v as u
			cg_edges[idv] = u;		
			//Adjust position
			while (idv >= cg_pstart[x] && idv < cg_pend[x]){
				if (idv > cg_pstart[x] && cg_edges[idv - 1]  > cg_edges[idv]){
					swap(cg_edges[idv], cg_edges[idv-1]); --idv;
				}else if (idv < cg_pend[x] -1 && cg_edges[idv + 1] < cg_edges[idv]){
					swap(cg_edges[idv + 1], cg_edges[idv]); ++idv;
				}else break;
			}			
		}else{
			printf("ERROR\n");
			exit(0);
		}
		/*printf("x %d:", x);
		for (ui i = cg_pstart[x]; i < cg_pend[x]; i++)
			printf("%d ", cg_edges[i]);
		printf("\n");*/
	}
	ecnt -= cg_deg(u);
	cg_pstart[u] = cg_pstart[w];
	cg_pend[u] = cg_pend[w];	
	ecnt -= cg_deg(v);
	cg_nbedges += ecnt;

	cg_pend[v] = cg_pstart[v];//invalidate v
	cg_valid[v] = 0;
	--cg_nbvtx;
	return u;
}

/**
 * make a copy of g into current graph : cg
 * In cg: the neigbors of u is located from cg_edges[cg_pstart[u]] to cg_edges[cg_pend[u]]. 
 * These vertices in [cg_pstart[u]] to cg_edges[cg_pend[u]] sorted in ascending order, all of them are vaid.
 * 
 * cg_nbvtx: is the number of vertex in cg. cg_maxvtx is the maximum vertex id in cg. A vertex id x is a valid vertex in cg 
 * 	if only if cg_valid[x]==true.
 */
void cg_prepareTempGraph(const MCsrGraph &g){

	cg_pstart = new int[g.nbvtx+1];
	cg_pend = new int[g.nbvtx+1];

	cg_MAXNBEDGES = 4 *g.nbedges;
	cg_edges = new ui[cg_MAXNBEDGES]; // extending the list
	cg_valid = new int[g.nbvtx];
	cg_nbvtx = g.nbvtx;
	cg_maxvtx = g.nbvtx;// change
	cg_nbedges = g.nbedges;
	cg_maxedge = g.nbedges;
	memcpy(cg_edges, g.edges, sizeof(ui) * g.nbedges);
	for (ui u= 0; u < g.nbvtx; u++){
		cg_vmp[u].push_back(u);
		cg_pstart[u] = g.pstart[u];
		cg_pend[u] = g.pstart[u+1];		
		cg_valid[u] = 1;
		sort(cg_edges + cg_pstart[u], cg_edges + cg_pend[u]);
	}
}

void cg_back2CSRGraph(MCsrGraph &g, map<ui, ui> &idtbl, int lb){
	if(cg_maxvtx <= lb || cg_nbvtx <= lb) {
		cg_maxedge = 0;
		cg_maxvtx = 0;
		cg_nbvtx = 0;
		cg_nbedges = 0;
	}
	ui *newid = new ui[cg_maxvtx];
	ui *orid = new ui[cg_nbvtx];
	//reorder the vertices
	int cnt = 0;
	for (ui u = 0; u < cg_maxvtx; u++){
		if (cg_valid[u]) {
			newid[u] = cnt;
			orid[cnt] = idtbl[u];
			++cnt;
		}else{
			newid[u] = cg_nbvtx; // 
		}
	}

	/*for (ui u = 0; u < cg_maxvtx; u++){
		if (!cg_valid[u]) newid[u] = cnt++;
	}*/

	assert(cnt == cg_nbvtx);
	g.nbvtx = cg_nbvtx;
	g.nbedges = cg_nbedges;
	g.pstart = new int[g.nbvtx + 1];
	g.edges = new ui[g.nbedges];
	g.pstart[0] = 0;
	int ecnt = 0;
	for (ui u = 0; u < cg_maxvtx; u++)	{
		if (cg_valid[u]){
			ui neu = newid[u];
			g.pstart[neu+1] = g.pstart[neu];
			for (int j = cg_pstart[u]; j < cg_pend[u]; j++){
				assert(newid[cg_edges[j]] != cg_nbvtx);
				g.edges[g.pstart[neu+1]++] = newid[cg_edges[j]];
				ecnt++;
			}
			assert(cg_deg(u) == g.degree(neu));
		}
	}
	assert(g.pstart[g.nbvtx] == ecnt);
	assert(g.nbvtx == cg_nbvtx);
	delete[] newid;
	//re id the vertices
	idtbl.clear();
	for (ui i = 0;i < g.nbvtx; i++){
		idtbl[i] = orid[i];
	}
}

void cg_checkConsistency(){
	int ecnt = 0;
	for (ui u = 0; u < cg_maxvtx; u++){
		if (!cg_valid[u]){
			assert(cg_pstart[u]== cg_pend[u]);
		}
		if(cg_valid[u]){
			for (ui j = cg_pstart[u]; j < cg_pend[u]; j++){
				assert(cg_valid[cg_edges[j]]);
				//ascending order				
				if (j < cg_pend[u] -1) assert(cg_edges[j] < cg_edges[j+1]); 
				ecnt++;
			}
		}
	}
	//printf("%d - %d\n", ecnt, cg_nbedges);
	assert(ecnt == cg_nbedges);
	printf("Consistent\n");
}
void testCGfunctions(const MCsrGraph &g){
	cg_prepareTempGraph(g);
	for (ui i = cg_pstart[1]; i < cg_pend[1]; i++) printf("%d ", cg_edges[i]);
	printf("\n");
	for (ui i = cg_pstart[26]; i < cg_pend[26]; i++) printf("%d ", cg_edges[i]);
	printf("\n");
	//cg_removeEdge(1,cg_pstart[1]+2);
	//cg_removeEdge(1,cg_pstart[1]);
	cg_mergeVtx(1, 26);
	for (ui i = cg_pstart[1]; i < cg_pend[1]; i++) printf("%d ", cg_edges[i]);
	printf("\n");
	cg_checkConsistency();
	exit(0);
}

void cg_edgeReduction(int K, int lb){
	int *triangles = new int[cg_MAXNBEDGES];	
	set<ui> Q1;
	while(true){
		if(!Q1.empty()){						
			ui u = *(Q1.begin());			
			Q1.erase(Q1.begin());
			int st = cg_pstart[u], end=cg_pend[u];
			cg_removeVtx(u);

			for (int i =  st; i < end; i++){
				ui v = cg_edges[i];								
				if (Q1.find(v) == Q1.end() && cg_deg(v) + K <= lb ){
					Q1.insert(v);						
				}
			}			
		}
		else{
			cg_countingTriangles(triangles);			
			set<pair<ui, ui> > egs;
			for (ui u = 0; u < cg_maxvtx; u++){
				if (cg_valid[u]){
					for (int j = cg_pstart[u]; j < cg_pend[u]; j++){
						if (u < cg_edges[j] && triangles[j] + 2* K <= lb){
							assert(triangles[j] != -1);
							//cg_removeEdge(u, j); //WARNING: inconsistency
							egs.insert(make_pair(u, cg_edges[j]));							
						}
					}
				}
			}
			set<ui> vts;
			for (auto e: egs){ 
				cg_removeEdge(e.first, e.second);				
				vts.insert(e.first); vts.insert(e.second);
			}		
			for (auto v: vts){
				if (cg_deg(v) + K <= lb){
					Q1.insert(v);
				}
			}
			if (Q1.empty())
				break;
		}		
	}
	delete[] triangles;
}

//TODO:
void cg_2hopReduction(int K, int lb, map<ui, vector<ui>> &idtbl){
	if (lb <= 2* K - 2){
		return;
	}
	for (ui u =0 ;u <cg_maxvtx; u++){
		if (cg_valid[u] ){
			map<ui, int> mapcom;
			for (int j = cg_pstart[u]; j < cg_pend[u]; j++){
				ui neiu = cg_edges[j];
				for (int k = cg_pstart[neiu]; k < cg_pend[neiu]; k++){
					int nei2hop = cg_edges[k];	
					bool isneiu = binary_search(cg_edges + cg_pstart[u], cg_edges + cg_pend[u], nei2hop);
					if (!isneiu)
						if (mapcom.find(nei2hop) != mapcom.end()){
							mapcom[nei2hop] ++;
						}else{
							mapcom[nei2hop] = 1;
						}					 							
				}
			}
			int canreduce = 0;
			for (auto x: mapcom){
				
			}
		}
	}
}

void strongReduction(const MCsrGraph &g, MCsrGraph &newG, int K, int lb, map<ui, ui> &idtbl){
	 //triangle counting
	//assert(seq != nullptr && core != nullptr && pos != nullptr);
	cg_prepareTempGraph(g);	
	cg_edgeReduction(K, lb);
	cg_back2CSRGraph(newG, idtbl, lb);
}

void peelReduction(const MCsrGraph &g, MCsrGraph &newG, int K, int lb, map<ui,ui> &idtbl){
	int *core = new int[g.nbvtx];
	ui *seq = new ui[g.nbvtx];
	int *pos = new int[g.nbvtx];
	coreDecomposition(g, core, seq, pos);

	ui *indvtx = new ui[g.nbvtx];
	ui szvtx = 0;
	for (int i = 0; i < g.nbvtx; i++){
		if (core[seq[i]] + K > lb ){
			indvtx[szvtx++] = seq[i];			
		}
	}
	induceSubgraph(g, newG, indvtx, szvtx, idtbl, lb);

	delete[] indvtx;
	delete[] core;
	delete[] seq;
	delete[] pos;
	
}

MCsrGraph orG; 		//original graph
MCsrGraph coreG;	//The graph after peeling
MCsrGraph kernalG; //After strong reduction
map<ui, ui> idtable;
ui* bestsol; // the best known solution
ui szbest;
int optimal = 0; //indicating if the best known solution is optimal

void massiveMKplex(){
	orG.fromBinaryFile(filename);
    printf("input graph n=%d, m=%d (undirected)\n", orG.nbvtx, orG.nbedges);	
	bestsol = new ui[orG.nbvtx];
	szbest = 0;

	clock_t stclk = clock();
	FastHeuSearch heusearch(orG, paraK);
	heusearch.coreHeurSolution();
	clock_t endheuclk = clock();

	szbest = heusearch.szsol;	
	copy(heusearch.sol, heusearch.sol + szbest, bestsol); 

	peelReduction(orG, coreG, paraK, szbest, idtable);
	clock_t endpeel = clock();
	printf("Core graph n=%d m=%d, peelTime=%.2f\n", coreG.nbvtx, coreG.nbedges, 
					Utility::elapse_seconds(endheuclk, endpeel));

	//strong reduction
	if (paraReductLevel == 2){
		strongReduction(coreG, kernalG, paraK, heusearch.szsol, idtable);		
		printf("Kernal graph n:%d e:%d time:%.2f\n", kernalG.nbvtx, kernalG.nbedges, Utility::elapse_seconds(endpeel, clock()));
	}else if (paraReductLevel == 1){
		kernalG = coreG;
	}
  
  //if (kernalG.nbvtx >= 500000){
  //  cout << "Out of memory!" << endl;
  //  return;
  //}
  
	clock_t strongclk = clock();
	//kernalG.toBinaryFile(strcat(filename, ".ker"));
	FastExactSearch2 *fes = nullptr;
	if (kernalG.nbvtx <= heusearch.szsol){
		optimal = 1;
	}else{	
		fes = new FastExactSearch2(kernalG, paraK, maxsec, heusearch.szsol);	
		fes->search();
		if (szbest < fes->szsol){
			szbest = fes->szsol;
			for (ui i = 0; i < fes->szsol; i++){
				bestsol[i] = idtable[fes->sol[i]];
			}
		}
		optimal = fes->isoptimal;
	}
	clock_t endclk = clock();
	if(0 == verifyKplex(orG, paraK, bestsol, szbest)){
		printf("Wrong answer\n");
		exit(1);
	}

	printf("\n");
	printf("#File=%s\n", Utility::basename(filename));
	printf("#K=%d\n", paraK);
	printf("#nodes=%d\n", orG.nbvtx);
	printf("#nedges=%d\n", orG.nbedges);

	printf("\n");
	printf("#heusol=%d\n", heusearch.szsol);
	printf("#heutime=%.2f\n", Utility::elapse_seconds(endheuclk, stclk));

	printf("\n");
	printf("#corennode=%d\n", coreG.nbvtx);
	printf("#corenedges=%d\n", coreG.nbedges);
	printf("#peeltime=%.2f\n", Utility::elapse_seconds(endheuclk, endpeel));

	printf("\n");
	printf("#kernalnnode=%d\n", kernalG.nbvtx);
	printf("#kernaldges=%d\n", kernalG.nbedges);
	printf("#strongredtime=%.2f\n", Utility::elapse_seconds(endpeel, strongclk));

	printf("\n");
	printf("#optimal=%d\n", optimal);
	if (fes != nullptr){
		printf("#branches=%lld\n", fes->nnodes);
		printf("#searchtime=%.2f\n",fes->getRunningTime());	
	}else{
		printf("#branches=0\n");
		printf("#searchtime=0.0\n");		
	}
  
	printf("\n");
	printf("#bestsol=%d\n", szbest);
	printf("#totime=%.2f\n", Utility::elapse_seconds(stclk, endclk));
	for (int i = 0; i < szbest; i++) {
		printf("%d ", bestsol[i]);
	}
	printf("\n\n\n");
	delete fes;
}


void usage() {
	printf("mkplex filename k <cuttime (default 100s)> <update (default off)>\n");
}
int main(int argc, char** argv) {
	//testMBitSet();
#ifndef DEBUGRUN
	if (argc >= 3) {
		strncpy(filename, argv[1], 1024);
		paraK = atoi(argv[2]);
		if (argc >= 4) {
			maxsec = atoi(argv[3]);
		}
		if (argc >= 5){
			paraReductLevel = atoi(argv[4]);
		}
	}
	else {
		usage();
		exit(1);
	}
#endif
	massiveMKplex();

	return 0;
}

