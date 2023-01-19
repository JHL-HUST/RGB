#pragma once 
#include <algorithm>
#include "Utility.h"
#include "MBitSet.h"
class  MBitGraph;
class MCsrGraph{
public:
	int nbedges;
	int nbvtx;
	int *pstart;
	ui *edges;
    
    MCsrGraph():nbvtx(0),nbedges(0),pstart(nullptr),edges(nullptr){}
    MCsrGraph(const MCsrGraph& csrg): nbvtx(csrg.nbvtx), nbedges(csrg.nbedges){
        pstart = new int[nbvtx+1];
        edges = new ui[nbedges];
        memcpy(pstart, csrg.pstart, sizeof(int) * (nbvtx+1));
        memcpy(edges, csrg.edges, sizeof(ui) * nbedges);
    }
    MCsrGraph& operator=(const MCsrGraph &g){
        if (pstart != nullptr) delete[] pstart;
        if (edges != nullptr) delete[] edges;
        nbvtx = g.nbvtx;
        nbedges = g.nbedges;
        pstart = new int[nbvtx+1];
        edges = new ui[nbedges];
        memcpy(pstart, g.pstart, sizeof(int) * (nbvtx+1));
        memcpy(edges, g.edges, sizeof(ui) * nbedges);
        return *this;
    }
    
    MCsrGraph(const MBitGraph& bitg);
    void fromBinaryFile(const char* filepath) {
        FILE *f = Utility::open_file(filepath, "rb");
        ui tt;
        fread(&tt, sizeof(ui), 1, f);
        if (tt != sizeof(ui)) {
            printf("sizeof unsigned int is different: file %u, machine %lu\n", tt, sizeof(ui));
        }
        
        fread(&nbvtx, sizeof(ui), 1, f);	// the number of vertices
        fread(&nbedges, sizeof(ui), 1, f); // the number of edges (twice the acutal number).
 
        ui *degree = new ui[nbvtx];
        fread(degree, sizeof(ui), nbvtx, f);
        if (pstart != nullptr) delete[] pstart;
        pstart = new int[nbvtx + 1];
        if (edges != nullptr) delete[] edges;
        edges = new ui[nbedges];

        //if (reverse != nullptr) delete[] reverse;
        //reverse = new ui[m];
        pstart[0] = 0;
        for (ui i = 0; i < nbvtx; i++) {
            if (degree[i] > 0){
                fread(edges + pstart[i], sizeof(ui), degree[i], f);
                //std::sort(edges+pstart[i], edges + pstart[i] + degree[i]);
            }
            pstart[i + 1] = pstart[i] + degree[i];
        }
        fclose(f);        
        //build complement graph matrix
        delete[] degree; 
    }
    
    void toBinaryFile(const char* filepath){
        FILE *f = Utility::open_file(filepath, "wb");
        ui tt = sizeof(ui);
        fwrite(&tt, sizeof(ui), 1, f); //length of ui
        fwrite(&nbvtx, sizeof(ui), 1, f);
        fwrite(&nbedges, sizeof(ui), 1, f);
        ui *d = new ui[nbvtx];
        for (ui i = 0; i < nbvtx; i++) d[i] =degree(i);
        fwrite(d, sizeof(ui), nbvtx, f);
        fwrite(edges, sizeof(ui), nbedges, f);
        fclose(f);
    }

    
    void reverseGraph(){
        fprintf(stderr, "function not implemented\n" );
        exit(1);
    }

    int degree(ui u) const{
        assert(u >= 0 && u < nbvtx);
        return pstart[u+1]-pstart[u];
    }
};

class MBitGraph{
public:
    int nbvtx;
    int nbedges;
    MBitSet64 **rows;

    MBitGraph():nbvtx(0), nbedges(0), rows(nullptr){}
    
    MBitGraph(const MBitGraph &mbg){
        nbvtx = mbg.nbvtx;
        nbedges = mbg.nbedges;
        rows = new MBitSet64*[nbvtx];
        for (int i = 0; i < nbvtx; i++){
            rows[i] = new MBitSet64(*(mbg.rows[i]));
        }
    }
    
    MBitGraph& operator=(const MBitGraph &mbg) = delete;
    //use operator =?
    MBitGraph(const MCsrGraph& cg){
        nbvtx = cg.nbvtx;
        nbedges = cg.nbedges;
        rows = new MBitSet64*[nbvtx];
        assert(rows!=nullptr);
        for (int i = 0; i < nbvtx; i++){
            rows[i] = new MBitSet64(nbvtx);
            for (int j = cg.pstart[i]; j < cg.pstart[i+1]; j++){
                rows[i]->set(cg.edges[j]);
            }
        }
        //degree = new int[nbvtx];
        //memcpy(degree, cg.degree, sizeof(int)*nbvtx);
    }
    
    //use operator ~?
    void reverseGraph(){
        for (int i = 0; i < nbvtx; i++){
            rows[i]->flip();
            rows[i]->set(i); 
           //degree[i] = nbvtx - degree[i] -1;
        }
        nbedges = nbvtx * (nbvtx - 1) - nbedges;
    }
    
    void writeToFile(char *filename){
        fprintf(stderr, "function  not implemented\n");
        exit(1);
    }

    int degree(int u){
        return rows[u]->size();
    }

    ~MBitGraph(){
        //delete[] degree;
        for (int i = 0; i < nbvtx; i++)
            delete rows[i];
        delete[] rows;
        nbvtx = nbedges = 0;
    }

};
extern int countIntersect(ui *lst1, int sz1, ui *lst2, int sz2);
extern int coreDecomposition(const MCsrGraph &g, int *core, ui* coreIncSeq, int *pos);
extern void countingTriangles(const MCsrGraph &g, int *pos, int *triangles);
extern ui* bsearch_with_index(ui* first, ui* last, ui data);