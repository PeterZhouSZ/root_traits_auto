// root_traits_auto.cpp
// This code takes as input a skeleton .ply file, and outputs a set of traits.
// Currently (10/27/2020), only the average branch length is computed, as a number printed out.
//
// Dan Zeng, danzeng@wustl.edu

#define USE_MATH_DEFINES

#include "stdafx.h"
#include <plyall.h>
#include <ply.h>
#include <string>
#include <map>
#include <vector>
#include <fstream>
#include <queue>
#define BOOST_TYPEOF_EMULATION
#include <algorithm>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/kruskal_min_spanning_tree.hpp>
#include <boost/graph/filtered_graph.hpp>
#include <boost/graph/connected_components.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/dijkstra_shortest_paths.hpp>
#include <boost/property_map/property_map.hpp>
#include <math.h>
#include "alglibinternal.h"
#include "linalg.h"
#include "dataanalysis.h"
# define M_PI           3.14159265358979323846

using namespace std;

struct internal {
	struct Vertex { float x, y, z; };
	struct Edge { int v1, v2; };
	struct Face {
		unsigned char nvts;
		int verts[3];
		float s;
	};
};
struct VertexWithMsure
{
	float width, radius;
	int stem = 0;
	float x, y, z;
	float compType;
	int inDiameter;
	float geodesicDistance;
	int level;

};

struct Branch {
	int fork;
	int tip;
	float length;
	float tipGeodesicDepth;
	int level;
	int parent;
	bool valid;
	std::vector<int> positions;
	float avgRadius = 0.0;
	std::vector<int> children;

};

using namespace boost;
struct VertexProperties {
	int degree;
	int burnTime;
};
typedef adjacency_list < vecS, vecS, undirectedS, VertexProperties, property < edge_weight_t, float > > Graph;

typedef graph_traits < Graph >::edge_descriptor Edge;

typedef graph_traits < Graph >::vertex_descriptor Vertex;

typedef graph_traits< Graph >::vertex_descriptor vertex_descriptor;

bool sortbysec(const std::tuple<int, float>& a, const std::tuple<int, float>& b)
{
	return (get<1>(a) < get<1>(b));
}

typedef std::pair<int, int> E;

float euclideanDistance(VertexWithMsure v1, VertexWithMsure v2) {
	return sqrtf((v1.x - v2.x) * (v1.x - v2.x) + (v1.y - v2.y) * (v1.y - v2.y) + (v1.z - v2.z) * (v1.z - v2.z));
}

bool compareByLevel(const Branch& a, const Branch& b)
{
	return a.level < b.level;
};

void fillComponentIterative(std::map<int, int>& visitedMap, int i, std::map<int, std::vector<int> > vertEdgeMapping, std::vector<internal::Edge> edges, std::vector<int> vertComps, std::vector<int>& newEdgeComp, std::vector<int>& newVertComp, float lowerRadiiThresh, vector<VertexWithMsure> vts) {

	//BFS to find high radius component of edges and vertices
	std::queue<int> vQ;
	vQ.push(i);
	while (!vQ.empty()) {
		int node = vQ.front();
		vQ.pop();
		//if (visitedMap.find(node) == visitedMap.end()) {
		visitedMap[node] = true;
		newVertComp.push_back(node);
		for (int j = 0; j < vertEdgeMapping[node].size(); j++) {

			int eIndex = vertEdgeMapping[node][j];
			//Choose endpoint of edge which hasn't been visited yet
			if (visitedMap.find(edges[eIndex].v1) == visitedMap.end()) {
				//Stop visiting edges when radius decreases below threshold
				if (vts[edges[eIndex].v1].radius > lowerRadiiThresh) {
					newEdgeComp.push_back(eIndex);

					vQ.push(edges[eIndex].v1);
				}
			}

			if (visitedMap.find(edges[eIndex].v2) == visitedMap.end()) {
				//Stop visiting edges when radius decreases below threshold
				if (vts[edges[eIndex].v2].radius > lowerRadiiThresh) {
					newEdgeComp.push_back(eIndex);
					vQ.push(edges[eIndex].v2);
				}
			}
		}
		//}
	}

}

float getLengthOfComponent(std::vector<int> compEdges, std::vector<internal::Edge> edges, std::vector<VertexWithMsure> vertices) {
	float dist = 0.0;

	for (int i = 0; i < compEdges.size(); i++) {
		dist += euclideanDistance(vertices[edges[compEdges[i]].v1], vertices[edges[compEdges[i]].v2]);
	}
	return dist;
}

float gaussianFactor(float val, float factor) {
	return exp(-(val * val) / 2.0 * factor * factor);
}

float getRangeScore(vector< vector<E> >& mstVertexEdges, int seedVertex, vector<VertexWithMsure>& allVertices, map<int, bool>& vertexInDiameter, int range) {
	int currentSeed = seedVertex;
	int ct = 0;
	float avgRadii = 0.0;
	map<int, bool> inRangeAlready;
	std::queue<int> currentSeeds; currentSeeds.push(currentSeed);
	vector<int> nextSeeds;
	while (!currentSeeds.empty() && ct < range) {

		currentSeed = currentSeeds.front();
		ct += 1;
		currentSeeds.pop();
		avgRadii += allVertices[currentSeed].radius;

		vector<E> vertEdges = mstVertexEdges[currentSeed];
		E currentEdge;
		for (int j = 0; j < vertEdges.size(); j++) {
			currentEdge = vertEdges[j];
			int nextSeed;
			if (currentEdge.first == currentSeed) {
				nextSeed = currentEdge.second;

			}
			else {
				nextSeed = currentEdge.first;
			}
			if (inRangeAlready.find(nextSeed) == inRangeAlready.end()) {

				if (vertexInDiameter.find(nextSeed) == vertexInDiameter.end()) {

					nextSeeds.push_back(nextSeed);
				}
			}
		}
	}
	for (int l = 0; l < nextSeeds.size(); l++) {
		currentSeeds.push(nextSeeds[l]);
	}

	inRangeAlready.clear();
	return avgRadii / (float)ct;
}
/**void dfs(grapht & g, int v, std::vector<bool> & visited, int & timer, int p, int & overallIndex, std::vector<node> & nodes) {
	visited[v] = true;
	nodes[v].compIndex = overallIndex;
	nodes[v].tin = timer; nodes[v].low = timer;
	timer += 1;
	int children = 0;
	auto neighbours = adjacent_vertices(v, g);
	for (auto u : make_iterator_range(neighbours)) {
		if (u != p) {
			if (visited[u]) {
				nodes[v].low = min(nodes[v].low, nodes[u].tin);
			}
			else {
				dfs(g, u, visited, timer, v, overallIndex, nodes);
				nodes[v].low = min(nodes[v].low, nodes[u].low);
				if (nodes[u].low >= nodes[v].tin) {
					if (nodes[u].tin > 1) {
						nodes[u].isNew = true;
					}
					if (p != -1) {
						nodes[v].isArticulate = true;
					}
				}
				children += 1;
			}
		}
	}
	if (p == -1 && children > 1) {
		nodes[v].isArticulate = true;
	}
}**/


//Return next forking point, find length of this segment
int travelSegment(Graph& g, vector<bool>& visited, vector<int>& depthMap, int i, int depth, std::vector<VertexWithMsure>& vts, std::vector<Branch>& branches, int branchIndex,
	std::vector<float>& dir, map<int, int>& branchPtr
) {
	std::queue<int> q;
	q.push(i);
	int fork = i;
	branches[branchIndex].tip = i;

	std::vector<int> path;
	while (!q.empty()) {
		int v = q.front();
		branchPtr[v] = branchIndex;
		path.push_back(v);
		branches[branchIndex].positions.push_back(v);
		branches[branchIndex].avgRadius += vts[v].radius;
		q.pop();
		depthMap[v] = depth;
		visited[v] = true;
		vts[v].width = depth;
		fork = v;
		auto neighbours = adjacent_vertices(v, g);
		for (auto u : make_iterator_range(neighbours)) {
			if (!visited[u]) {
				q.push(u);
			}

		}

		if (q.size() > 1) {
			break;
		}
		if (q.size() == 1) {
			branches[branchIndex].length = branches[branchIndex].length + euclideanDistance(vts[v], vts[q.front()]);
			//std::cout << "length of branch " << branchIndex << " updated to " << branches[branchIndex].length << std::endl;
			branches[branchIndex].tipGeodesicDepth = branches[branchIndex].tipGeodesicDepth + euclideanDistance(vts[v], vts[q.front()]);
			branches[branchIndex].tip = q.front();
			/**if (length > 500) {
				fork = -1;
				break;
			}**/
		}
	}
	dir = { vts[path.size() - 1].x - vts[path[0]].x, vts[path.size() - 1].y - vts[path[0]].y, vts[path.size() - 1].z - vts[path[0]].z };
	return fork;
}

void updateSubtree(Graph& g, vector<int>& depthMap, int i, int depth, std::vector<VertexWithMsure>& vts, map<int, int>& branchPtr,
	int parentBranchIndex, std::vector<Branch>& branches) {
	std::queue<int> q;
	q.push(i);
	map<int, bool> visited;
	map<int, bool> branchDecremented;
	while (!q.empty()) {
		int v = q.front();
		q.pop();
		//std::cout << "levels " << branches[branchPtr[v]].level << " " << depthMap[v] << " " << branches[parentBranchIndex].level << " " << depth << std::endl;
		if (depthMap[v] == depth + 1) {
			branches[branchPtr[v]].valid = false;
			//std::cout << "Set to invalid " << branchPtr[v] << " " << branches[branchPtr[v]].valid << std::endl;
			branchPtr[v] = parentBranchIndex;
		}
		if (depthMap[v] == depth + 2) {
			branches[branchPtr[v]].parent = parentBranchIndex;
		}

		if (branches[branchPtr[v]].level > depth) {
			if (branchDecremented.find(branchPtr[v]) == branchDecremented.end()) {
				branchDecremented[branchPtr[v]] = true;
				//std::cout << "branch " << branchPtr[v] << " currently at " << branches[branchPtr[v]].level << std::endl;
				branches[branchPtr[v]].level = branches[branchPtr[v]].level - 1;
				//std::cout << "branch decremented " << branches[branchPtr[v]].level << std::endl;
			}
		}
		depthMap[v] = depthMap[v] - 1;

		//std::cout << "decremented to " << v << " to " << depthMap[v] << std::endl;
		vts[v].width = vts[v].width - 1;

		visited[v] = true;
		auto neighbours = adjacent_vertices(v, g);
		for (auto u : make_iterator_range(neighbours)) {
			//std::cout << u << " " << depthMap[u] << " " << depth << std::endl;
			if (depthMap[u] > depth) {
				if (visited.find(u) == visited.end()) {
					q.push(u);
				}
			}
		}
	}
}

float dotProd(std::vector<float>& dir1, std::vector<float>& dir2) {
	return dir1[0] * dir2[0] + dir1[1] * dir2[1] + dir1[2] * dir2[2];
}

float mag(std::vector<float>& dir) {
	return sqrt(dir[0] * dir[0] + dir[1] * dir[1] + dir[2] * dir[2]);
}

float angle(std::vector<float>& dir1, std::vector<float>& dir2) {
	return acos(dotProd(dir1, dir2) / (mag(dir1) * mag(dir2)));
}

void normalize(std::vector<float>& vec) {
	float magnitude = mag(vec);
	for (int i = 0; i < vec.size(); i++) {
		vec[i] = vec[i] / magnitude;
	}
}

int buildHierarchy(Graph& g, vector<bool>& visited, vector<int>& depthMap, int i, int depth, std::vector<VertexWithMsure>& vts,
	std::vector<float>& outDir, std::vector<Branch>& branches, int parentBranch, map<int, int>& branchPtr) {
	std::vector<float> dir(3, 0);
	int fork = travelSegment(g, visited, depthMap, i, depth, vts, branches, parentBranch, dir, branchPtr);

	outDir = dir;
	auto neighbours = adjacent_vertices(fork, g);
	int maxDepth = depth;
	int bestPathRoot = -1;
	float bestSubLength = 0.0;
	float bestScore = 0.0;
	int bestBranch = -1;
	std::vector<int> potentialBranches;
	for (auto u : make_iterator_range(neighbours)) {
		if (!visited[u]) {
			std::vector<float> subDir(3, 0);
			Branch child;
			child.fork = fork;
			child.tip = u;
			child.length = euclideanDistance(vts[fork], vts[u]);
			child.tipGeodesicDepth = branches[parentBranch].tipGeodesicDepth + euclideanDistance(vts[fork], vts[u]);
			child.level = depth + 1;
			child.valid = true;
			branches.push_back(child);
			potentialBranches.push_back(branches.size() - 1);
			int topoDepth = buildHierarchy(g, visited, depthMap, u, child.level, vts, subDir, branches, branches.size() - 1, branchPtr);
			float subAngle = angle(outDir, subDir);
			float score = gaussianFactor(subAngle, 0.3) * branches[potentialBranches[potentialBranches.size() - 1]].length;

			if (topoDepth > maxDepth) {
				maxDepth = topoDepth;
				bestPathRoot = u;
				bestSubLength = child.length;
				bestScore = score;
				bestBranch = potentialBranches.size() - 1;
			}
			else {
				if (topoDepth == maxDepth) {
					if (score > bestScore) {
						maxDepth = topoDepth;
						bestPathRoot = u;
						bestSubLength = child.length;
						bestScore = score;
						bestBranch = potentialBranches.size() - 1;
					}
				}
			}
		}
	}

	if (bestPathRoot != -1) {
		//Update hierarchy under subtree
		//cout << "updating subtree " << parentBranch << " " << bestSubLength << endl;
		updateSubtree(g, depthMap, bestPathRoot, depth, vts, branchPtr, parentBranch, branches);

		for (int j = 0; j < potentialBranches.size(); j++) {
			//std::cout << "Potential branch " << j << " " << bestBranch << std::endl;
			if (j != bestBranch) {
				branches[potentialBranches[j]].parent = parentBranch;
				branches[parentBranch].children.push_back(potentialBranches[j]);
				//branches[potentialBranches[j]].valid = true;
			}
			else {
				branches[potentialBranches[j]].parent = -1;
				branches[potentialBranches[j]].valid = false;

				branches[parentBranch].length = branches[parentBranch].length + branches[potentialBranches[j]].length;
				branches[parentBranch].tipGeodesicDepth = branches[potentialBranches[j]].tipGeodesicDepth;
				branches[parentBranch].tip = branches[potentialBranches[j]].tip;


				for (int k = 0; k < branches[potentialBranches[j]].positions.size(); k++) {
					branches[parentBranch].positions.push_back(branches[potentialBranches[j]].positions[k]);
					branches[parentBranch].avgRadius += vts[branches[potentialBranches[j]].positions[k]].radius;
				}
				for (int k = 0; k < branches[potentialBranches[j]].children.size(); k++) {
					branches[parentBranch].children.push_back(branches[potentialBranches[j]].children[k]);
				}
			}
		}
	}

	return maxDepth;

}


/**
void buildBranchesFromJunction(Graph& g, vector<bool>& visited, vector<int>& depthMap, int stemIndex, int i, int depth, std::vector<VertexWithMsure>& vts,  float radiusTolerance) {

	std::queue<int> q;
	q.push(i);
	while (!q.empty()) {
		int v = q.front();
		q.pop();
		if (euclideanDistance(vts[v], vts[stemIndex]) > vts[stemIndex].radius * radiusTolerance) {
			//branchingPts.push_back(v);
			float length = 0.0;
			int newBranchDepth = 2;
			std::vector<float> dir = {vts[i].x - vts[stemIndex].x, vts[i].y - vts[stemIndex].y, vts[i].z - vts[stemIndex].z };
			buildHierarchy(g, visited, depthMap, v, newBranchDepth, vts, length, dir);

			std::cout << "primary branch of length " << length << std::endl;
		}
		else {
			depthMap[v] = depth+1;
			visited[v] = true;
			vts[v].width = depth+1;
			auto neighbours = adjacent_vertices(v, g);
			for (auto u : make_iterator_range(neighbours))
			{
				if (!visited[u]) {
					q.push(u);
				}
			}
		}
	}
	//for (int i = 0; i < branchingPts.size(); i++) {
		//buildHierarchy(g, visited, depthMap, junction, branchingPts[i], depth, vts, length);
	//}
}**/

void findStemSeeds(Graph& g, vector<bool>& visited, vector<int>& depthMap, int stemIndex, int i, int depth, std::vector<VertexWithMsure>& vts, float radiusTolerance, std::vector<int>& stemSeeds, std::vector<int>& junctions) {

	std::queue<int> q;
	q.push(i);
	while (!q.empty()) {
		int v = q.front();
		q.pop();
		if (euclideanDistance(vts[v], vts[stemIndex]) > vts[stemIndex].radius * radiusTolerance) {
			stemSeeds.push_back(v);
			junctions.push_back(stemIndex);
		}
		else {
			depthMap[v] = depth;
			visited[v] = true;
			vts[v].width = depth;
			auto neighbours = adjacent_vertices(v, g);
			for (auto u : make_iterator_range(neighbours))
			{
				if (!visited[u]) {
					q.push(u);
				}
			}
		}
	}
}

vector<string> split(const string& str, const string& delim)
{
	vector<string> tokens;
	size_t prev = 0, pos = 0;
	do
	{
		pos = str.find(delim, prev);
		if (pos == string::npos) pos = str.length();
		string token = str.substr(prev, pos - prev);
		if (!token.empty()) tokens.push_back(token);
		prev = pos + delim.length();
	} while (pos < str.length() && prev < str.length());
	return tokens;
}

int main(int argc, char** argv)
{

	std::map<std::string, PlyProperty> v_props_map;

	char* inFile = NULL;
	string outFile;
	string traitFile;
	bool fixStem = false;
	float radiusTolerance = 1.6;
	float upperRadiusRatio = 0.55;
	float lowerRadiusRatio = 0.15;
	int maxLevel = 5;
	bool branch = false;
	for (int i = 0; i < argc; i++) {
		if (((string)argv[i]).substr(0, 2) == "--") {
			string arg = (string)argv[i];
			arg.erase(0, 2);
			if (arg == "in") {
				inFile = argv[i + 1]; //Input skeleton file
			}
			if (arg == "out") {
				outFile = argv[i + 1]; //Output skeleton file:
			}
			if (arg == "traits") {
				traitFile = argv[i + 1]; //Output skeleton file:
			}
			if (arg == "fixStem") {
				fixStem = true;
			}
			if (arg == "radiusTolerance") {
				radiusTolerance = stof(argv[i + 1]);
			}
			if (arg == "upperRadius") {
				upperRadiusRatio = stof(argv[i + 1]);
			}
			if (arg == "lowerRadius") {
				lowerRadiusRatio = stof(argv[i + 1]);
			}

			if (arg == "branch") {
				branch = true;
			}

			if (arg == "maxLevel") {
				maxLevel = stoi(argv[i + 1]);
			}

		}
	}
	/**
	PlyProperty v_props[] = {
		{ (char*)"bt2", Float32, Float32, offsetof(VertexWithMsure, width), 0, 0, 0, 0 },
	{ (char*)"radius", Float32, Float32, offsetof(VertexWithMsure, radius), 0, 0, 0, 0 },
	//{ (char*)"bt1", Float32, Float32, offsetof(VertexWithMsure, bt1), 0, 0, 0, 0 },
	{ (char*)"x", Float32, Float32, offsetof(VertexWithMsure, x), 0, 0, 0, 0 },
	{ (char*)"y", Float32, Float32, offsetof(VertexWithMsure, y), 0, 0, 0, 0 },
	{ (char*)"z", Float32, Float32, offsetof(VertexWithMsure, z), 0, 0, 0, 0 },
	{ (char*)"eccentricity", Float32, Float32, offsetof(VertexWithMsure, eccentricity), 0, 0, 0, 0 },
	{ (char*)"rad-0", Float32, Float32, offsetof(VertexWithMsure, rad0), 0, 0, 0, 0 }
	};
	v_props_map["bt2"] = v_props[0];
	v_props_map["radius"] = v_props[1];
	v_props_map["x"] = v_props[2];
	v_props_map["y"] = v_props[3];
	v_props_map["z"] = v_props[4];
	v_props_map["eccentricity"] = v_props[6];
	v_props_map["rad0"] = v_props[7];**/
	PlyProperty v_props[] = {
	{ (char*)"radius", Float32, Float32, offsetof(VertexWithMsure, radius), 0, 0, 0, 0 },
	{ (char*)"bt2", Float32, Float32, offsetof(VertexWithMsure, width), 0, 0, 0, 0 },
	{ (char*)"x", Float32, Float32, offsetof(VertexWithMsure, x), 0, 0, 0, 0 },
	{ (char*)"y", Float32, Float32, offsetof(VertexWithMsure, y), 0, 0, 0, 0 },
	{ (char*)"z", Float32, Float32, offsetof(VertexWithMsure, z), 0, 0, 0, 0 }
	};

	v_props_map["radius"] = v_props[0];
	v_props_map["bt2"] = v_props[1];
	v_props_map["x"] = v_props[2];
	v_props_map["y"] = v_props[3];
	v_props_map["z"] = v_props[4];

	std::map<std::string, PlyProperty> e_props_map;
	PlyProperty e_props[] = {
		{ (char*)"vertex1", Int32, Int32, offsetof(internal::Edge, v1), PLY_SCALAR, 0, 0, 0 },
	{ (char*)"vertex2", Int32, Int32, offsetof(internal::Edge, v2), PLY_SCALAR, 0, 0, 0 }
	};
	e_props_map["vertex1"] = e_props[0];
	e_props_map["vertex2"] = e_props[1];
	std::map<std::string, PlyProperty> f_props_map;
	PlyProperty f_props[] = {
		(char*)"vertex_indices", Int32, Int32, offsetof(ply::Face, verts),
		PLY_LIST, Uint8, Uint8, offsetof(ply::Face,nvts) };
	f_props_map["vertex_indices"] = f_props[0];
	std::vector<VertexWithMsure> vts;
	std::vector<internal::Edge> edges;
	std::vector<internal::Face> faces;

	ply::PLYreader ply_reader;
	if (ply_reader.read(inFile, v_props_map, e_props_map, f_props_map, vts, edges, faces) != ply::SUCCESS)
	{
		std::cout << "failed to read mesh file " << inFile << std::endl;
	}

	std::map<int, std::vector<int> > vertIndexEdgeIndices;
	float totalDistance = 0.0;
	float upperRadiiThresh = 20.0;
	float lowerRadiiThresh = 5.0;
	float lowerStemThresh = 5.0;
	for (int i = 0; i < edges.size(); i++) {
		if (vertIndexEdgeIndices.find(edges[i].v1) == vertIndexEdgeIndices.end()) {
			std::vector<int> edgeIndices = { i };
			vertIndexEdgeIndices[edges[i].v1] = edgeIndices;
		}
		else {
			std::vector<int> edgeIndices = vertIndexEdgeIndices[edges[i].v1];
			edgeIndices.push_back(i);
			vertIndexEdgeIndices[edges[i].v1] = edgeIndices;
		}
		if (vertIndexEdgeIndices.find(edges[i].v2) == vertIndexEdgeIndices.end()) {
			std::vector<int> edgeIndices = { i };
			vertIndexEdgeIndices[edges[i].v2] = edgeIndices;

		}
		else {
			std::vector<int> edgeIndices = vertIndexEdgeIndices[edges[i].v2];
			edgeIndices.push_back(i);
			vertIndexEdgeIndices[edges[i].v2] = edgeIndices;
		}
		totalDistance += euclideanDistance(vts[edges[i].v1], vts[edges[i].v2]);


	}

	int highestRadEndPt = -1;
	int highestRadPt = 0;
	int numEndPts = 0;
	float highestRadius = 0.0;
	for (int i = 0; i < vts.size(); i++) {
		if (vertIndexEdgeIndices[i].size() == 1) {
			numEndPts++;
		}
		if (vertIndexEdgeIndices[i].size() == 1) {
			if (highestRadEndPt != -1) {
				if (vts[i].radius > vts[highestRadEndPt].radius) {
					highestRadEndPt = i;
				}
			}
			else {
				highestRadEndPt = i;
			}
		}

		if (vts[i].radius > vts[highestRadPt].radius) {
			highestRadPt = i;
		}
		highestRadius = max(vts[i].radius, highestRadius);
	}
	upperRadiiThresh = upperRadiusRatio * highestRadius;
	lowerRadiiThresh = lowerRadiusRatio * highestRadius;
	lowerStemThresh = 0.1 * highestRadius;

	std::cout << vts[highestRadPt].radius << " " << highestRadPt << std::endl;

	int maxRadiusVtIndex = 0;
	for (int i = 0; i < vts.size(); i++) {
		if (vts[i].radius > upperRadiiThresh) {
			vts[i].inDiameter = 1;
		}
		else {
			vts[i].inDiameter = -1;
		}
		if (vts[i].radius > vts[maxRadiusVtIndex].radius) {
			maxRadiusVtIndex = i;
		}
	}

	//Start stem search
	std::vector < std::tuple< std::vector<VertexWithMsure>, std::vector<int>, float> > potentialStemComponents;
	std::map<int, int> connectedVertexComponents;
	std::vector<int> vertComps;
	std::vector<int> edgeComps;
	//Find vertices with radius greater than upperRadiiThresh, and perform BFS to find high radius connected component starting from that vertex
	//For recording which vertices are in the stem (The stem is the graph diameter of the high radius region
	map<int, bool> vertexInDiameter;
	vector<int> diameterVts;
	for (int i = 0; i < vts.size(); i++) {

		//If haven't visited this vertex yet and above upperRadiiThresh, begin new component
		if (connectedVertexComponents.find(i) == connectedVertexComponents.end()) {
			if (vts[i].radius > upperRadiiThresh) {

				std::vector<int> newVertComp;
				std::vector<int> newEdgeComp;
				map<int, int> visitedMap = connectedVertexComponents;
				//Flood fill one component by traversing edges along skeleton
				fillComponentIterative(visitedMap, i, vertIndexEdgeIndices, edges, vertComps, newEdgeComp, newVertComp, lowerRadiiThresh, vts);

				//Optional step: threshold the largest components by the number of vertices
				float length = getLengthOfComponent(newEdgeComp, edges, vts);

				//Length threshold
				//if (length > 30) {

				//Add new connected component of vertices to component list
				std::vector<VertexWithMsure> vertPos;
				for (int j = 0; j < newVertComp.size(); j++) {
					vertPos.push_back(vts[newVertComp[j]]);
				}
				std::cout << "vert pos size " << vertPos.size() << std::endl;
				//potentialStemComponents.push_back(make_tuple(vertPos, newEdgeComp, length));
				//break;
				//}

				vector<int> stemEdgesT = newEdgeComp;
				std::vector<VertexWithMsure> stemVerticesT;
				std::vector<internal::Edge> stemEdgesRT;
				std::vector<internal::Face> stemFacesT;


				std::map<int, int> oldToNewVtIndex;


				std::vector<E> stemEdgesReindexed;

				//vector<float> weights;
				float* weights = new float[stemEdgesT.size()];

				E* edgePairs = new E[stemEdgesT.size()];
				map<E, float> edgeWeightMap;
				map<int, int> stemToOrigVertexMapping;
				for (int i = 0; i < stemEdgesT.size(); i++) {
					if (oldToNewVtIndex.find(edges[stemEdgesT[i]].v1) == oldToNewVtIndex.end()) {
						oldToNewVtIndex[edges[stemEdgesT[i]].v1] = stemVerticesT.size();
						stemToOrigVertexMapping[stemVerticesT.size()] = edges[stemEdgesT[i]].v1;
						stemVerticesT.push_back(vts[edges[stemEdgesT[i]].v1]);
						stemVerticesT[stemVerticesT.size() - 1].width = 1;
					}
					if (oldToNewVtIndex.find(edges[stemEdgesT[i]].v2) == oldToNewVtIndex.end()) {
						oldToNewVtIndex[edges[stemEdgesT[i]].v2] = stemVerticesT.size();
						stemToOrigVertexMapping[stemVerticesT.size()] = edges[stemEdgesT[i]].v2;
						stemVerticesT.push_back(vts[edges[stemEdgesT[i]].v2]);
						stemVerticesT[stemVerticesT.size() - 1].width = 1;
					}
					internal::Edge newE = edges[stemEdgesT[i]];
					newE.v1 = oldToNewVtIndex[edges[stemEdgesT[i]].v1];
					newE.v2 = oldToNewVtIndex[edges[stemEdgesT[i]].v2];
					edgePairs[i] = E(newE.v1, newE.v2);
					stemEdgesRT.push_back(newE);

					if (stemVerticesT[newE.v1].inDiameter == 1 || stemVerticesT[newE.v2].inDiameter == 1) {
						weights[i] = 0.0;
					}
					else {
						float avgRadius = (stemVerticesT[newE.v1].radius + stemVerticesT[newE.v2].radius) / 2.0;
						if (avgRadius < lowerStemThresh) {
							weights[i] = 100000;
						}
						else {
							weights[i] = gaussianFactor(avgRadius, 0.1);
						}
						edgeWeightMap[edgePairs[i]] = weights[i];
					}
				}

#if defined(BOOST_MSVC) && BOOST_MSVC <= 1300
				Graph g(vts.size());
				property_map<Graph, edge_weight_t>::type weightmap = get(edge_weight, g);
				for (std::size_t j = 0; j < stemEdges.size(); ++j) {
					Edge e; bool inserted;
					boost::tie(e, inserted) = add_edge(stemEdges[j].v1, stemEdges[j].v2s, g);
					weightmap[e] = weights[j];
				}
#else

				Graph g(edgePairs, edgePairs + stemEdgesT.size(), weights, stemVerticesT.size());
#endif
				std::vector < Edge > spanning_tree;
				map<int, int> vertBurnTimes;
				kruskal_minimum_spanning_tree(g, std::back_inserter(spanning_tree));

				stemEdgesT.clear(); stemEdgesT.shrink_to_fit();

				float* mstWeights = new float[spanning_tree.size()];
				E* spanningTreeEdges = new E[spanning_tree.size()];


				vector< vector<E> > mstVertEdges(vts.size());
				vector<internal::Edge> mstEdges;
				for (int i = 0; i < spanning_tree.size(); i++) {
					E edge = E(source(spanning_tree[i], g), target(spanning_tree[i], g));
					spanningTreeEdges[i] = edge;
					mstWeights[i] = edgeWeightMap[edge];
					mstVertEdges[source(spanning_tree[i], g)].push_back(edge);
					mstVertEdges[target(spanning_tree[i], g)].push_back(edge);
					internal::Edge e;
					e.v1 = source(spanning_tree[i], g); e.v2 = target(spanning_tree[i], g);
					mstEdges.push_back(e);
				}


				//Minimum spanning tree of high radius region -> this is a boost object
				Graph mst(spanningTreeEdges, spanningTreeEdges + spanning_tree.size(), mstWeights, stemVerticesT.size());

				//Temporary structure to keep track of edges during burning process
				Graph subGraph = mst;

				//Start burning process
				bool burnable = true;
				int burnRound = 0;
				vector< vector<E> > burnRoundMapping(100000);
				vector< vector<int> > burnRoundMappingVts(100000);
				vector<int> endPts;
				while (burnable) {
					vector<Edge> subgraphEdges;
					burnable = false;
					int burnableEdges = 0;
					vector<Edge> burnedEdges;
					for (int i = 0; i < spanning_tree.size(); i++) {

						E edge = E(source(spanning_tree[i], subGraph), target(spanning_tree[i], subGraph));
						spanningTreeEdges[i] = edge;

						//Optional: I assigned a special weight for each edge based on the surrounding radii, but you can just use the average radius of the edge vertices
						mstWeights[i] = edgeWeightMap[edge];

						//Implicitly perform burning by only preserving edges that are not part of endpoints for the next burning iteration
						if (subGraph.m_vertices[source(spanning_tree[i], subGraph)].m_out_edges.size() > 1 && subGraph.m_vertices[target(spanning_tree[i], subGraph)].m_out_edges.size() > 1) {
							subgraphEdges.push_back(spanning_tree[i]);
						}
						else {
							//Edge was burned this round: record the burn time of each edge
							burnRoundMapping[burnRound].push_back(edge);

							burnableEdges += 1;

							//Record when vertices are burned as well
							if (subGraph.m_vertices[source(spanning_tree[i], subGraph)].m_out_edges.size() == 1) {
								vertBurnTimes[source(spanning_tree[i], subGraph)] = burnRound;
								burnable = true;
								burnRoundMappingVts[burnRound].push_back(source(spanning_tree[i], subGraph));
							}
							if (subGraph.m_vertices[target(spanning_tree[i], subGraph)].m_out_edges.size() == 1) {
								vertBurnTimes[target(spanning_tree[i], subGraph)] = burnRound;
								burnable = true;
								burnRoundMappingVts[burnRound].push_back(target(spanning_tree[i], subGraph));
							}
							burnedEdges.push_back(spanning_tree[i]);

						}
					}
					//For debugging
					cout << "burnable edges " << burnableEdges << endl;

					if (subgraphEdges.size() <= 1) {
						burnable = false;
					}
					spanning_tree = subgraphEdges;
					//Remove burned edges from the graph
					for (int i = 0; i < burnedEdges.size(); i++) {
						remove_edge(source(burnedEdges[i], subGraph), target(burnedEdges[i], subGraph), subGraph);
					}
					burnRound += 1;

				}

				//Start inverse burn
				Graph diameterGraph;

				vector<E> diameterEdgeVec = burnRoundMapping[burnRound - 1];

				burnRound -= 1;

				//Find the vertices which were burned this round. These are the endpoints of the current iteration to expand the stem from
				vector<int> seedVertices = burnRoundMappingVts[burnRound];


				vector< vector<int> > branchEdges;
				int lowestSeedVert = 0;

				while (burnRound > 0) {
					cout << "burn round " << burnRound << endl;

					//Record the vertices and edges which are currently in the stem
					E* diameterEdges = new E[diameterEdgeVec.size()];
					float* diameterWeights = new float[diameterEdgeVec.size()];
					for (int i = 0; i < diameterEdgeVec.size(); i++) {
						diameterEdges[i] = diameterEdgeVec[i];

						//Optional part to weight edges based upon neighboring radii -> you dont need to include this
						diameterWeights[i] = edgeWeightMap[diameterEdgeVec[i]];
					}


					vector<int> nextSeedVertices;
					//Get edges for bordering vertices
					for (int i = 0; i < seedVertices.size(); i++) {

						//Add to stem
						vertexInDiameter[stemToOrigVertexMapping[seedVertices[i]]] = true;
						diameterVts.push_back(stemToOrigVertexMapping[seedVertices[i]]);
						connectedVertexComponents[stemToOrigVertexMapping[seedVertices[i]]] = 1;

						//Find edges adjacent to endpoints of stem so far
						vector<E> vertEdges = mstVertEdges[seedVertices[i]];
						float bestRadius = -1;
						int bestSeed = -1;
						E bestEdge;
						//Choose edge whose other endpoint has highest radius, and whose burn time is one less than the current one
						for (int j = 0; j < vertEdges.size(); j++) {
							E edge = vertEdges[j];
							int nextSeed = -1;
							if (vertBurnTimes[edge.first] == burnRound - 1) {
								nextSeed = edge.first;
							}
							if (vertBurnTimes[edge.second] == burnRound - 1) {
								nextSeed = edge.second;
							}
							if (nextSeed != -1) {
								if (vertexInDiameter.find(stemToOrigVertexMapping[nextSeed]) == vertexInDiameter.end()) {

									if (stemVerticesT[nextSeed].inDiameter == 1) {

										if (stemVerticesT[nextSeed].radius > bestRadius)
										{
											bestRadius = edgeWeightMap[edge];
											bestSeed = nextSeed;
											bestEdge = edge;
										}
									}
									else {
										//getRangeScore is just a scoring function for which vertex to choose to add to the stem. Just replace this with the vertex radius
										//getRangeScore(mstVertEdges, nextSeed, stemVertices, vertexInDiameter, 5)
										if (stemVerticesT[nextSeed].radius > bestRadius) {
											bestRadius = edgeWeightMap[edge];
											bestSeed = nextSeed;
											bestEdge = edge;
										}
									}

								}
							}

						}
						if (bestSeed > -1) {
							//Find edges for decremented burn time
							nextSeedVertices.push_back(bestSeed);
							diameterEdgeVec.push_back(bestEdge);

						}

					}

					//Decrement burn time
					seedVertices = nextSeedVertices;
					burnRound -= 1;
				}
				spanning_tree.clear();
			}

		}
	}

	//Find high-radius connected component with the largest size
	//std::sort(potentialStemComponents.begin(), potentialStemComponents.end(), [](auto const& t1, auto const& t2) {
		//return get<2>(t1) > get<2>(t2);
	//}
	//);


	/**std::cout << "stem components " << potentialStemComponents.size() << std::endl;
	for (int s = 0; s < potentialStemComponents.size(); s++) {
		vector<int> stemEdgesT = get<1>(potentialStemComponents[s]);


	}**/
	std::cout << "diameterVts size " << diameterVts.size() << std::endl;
	//Find distances from highest radius point to all other points
	cout << "Forcing highest radius endpoint to be on stem" << endl;
	int startVtx = highestRadEndPt;
	std::queue<int> diamSearchQ;
	diamSearchQ.push(startVtx);
	map<int, bool> diamVisited;
	map<int, float> parentDistDiam;
	parentDistDiam[startVtx] = 0.0;
	int diamVtsReached = 0;
	while (!diamSearchQ.empty()) {
		int currentVtx = diamSearchQ.front();
		diamSearchQ.pop();
		if (diamVisited.find(currentVtx) == diamVisited.end()) {
			diamVisited[currentVtx] = true;
			//if (vertexInDiameter.find(currentVtx) != vertexInDiameter.end()) {
			diamVtsReached += 1;
			int currentVtxOld = currentVtx;
			vector<int> neighborEdgesOldIndexing = vertIndexEdgeIndices[currentVtxOld];
			for (int i = 0; i < neighborEdgesOldIndexing.size(); i++) {
				int nVtx = -1;
				if (edges[neighborEdgesOldIndexing[i]].v1 != currentVtxOld) {
					nVtx = edges[neighborEdgesOldIndexing[i]].v1;
				}
				if (edges[neighborEdgesOldIndexing[i]].v2 != currentVtxOld) {
					nVtx = edges[neighborEdgesOldIndexing[i]].v2;
				}
				if (nVtx != -1) {
					if (vertexInDiameter.find(nVtx) != vertexInDiameter.end()) {
						int stemNIndex = nVtx;
						if (diamVisited.find(stemNIndex) == diamVisited.end()) {
							//if neighbor also in diameter, keep traversing
							parentDistDiam[stemNIndex] = parentDistDiam[currentVtx] + euclideanDistance(vts[currentVtx], vts[stemNIndex]);

							diamSearchQ.push(stemNIndex);
						}
					}
				}
			}

			//}
		}
	}
	float* weightsOriginal = new float[edges.size()];
	E* edgePairsOriginal = new E[edges.size()];
	for (int i = 0; i < edges.size(); i++) {
		edgePairsOriginal[i] = E(edges[i].v1, edges[i].v2);
		weightsOriginal[i] = euclideanDistance(vts[edges[i].v1], vts[edges[i].v2]);
	}
	Graph gOriginal(edgePairsOriginal, edgePairsOriginal + edges.size(), weightsOriginal, vts.size());
	if (fixStem) {
		/**int maxRadiusPt = diameterVts[0];
		float maxX = -1000; float maxY = -1000; float maxZ = -1000;
		float minX = 1000; float minY = 1000; float minZ = 1000;
		int firstEndPt = -1;
		for (int i = 0; i < diameterVts.size(); i++) {
			vts[diameterVts[i]].width = parentDistDiam[diameterVts[i]];
			maxX = max(maxX, vts[diameterVts[i]].x);
			maxY = max(maxY, vts[diameterVts[i]].y);
			maxZ = max(maxZ, vts[diameterVts[i]].z);

			minX = min(minX, vts[diameterVts[i]].x);
			minY = min(minY, vts[diameterVts[i]].y);
			minZ = min(minZ, vts[diameterVts[i]].z);

			if (vts[diameterVts[i]].radius > vts[maxRadiusPt].radius) {
				maxRadiusPt = diameterVts[i];
			}
			if (firstEndPt == -1) {
				firstEndPt = diameterVts[i];
				cout << "first end pt set " << firstEndPt << endl;
			}
			else {
				if (vts[diameterVts[i]].z < vts[firstEndPt].z) {
					firstEndPt = diameterVts[i];
					cout << "pt updated " << firstEndPt << endl;
				}
			}

		}
		cout << minX << " " << maxX << " " << minY << " " << maxY << " " << minZ << " " << maxZ <<
			" " <<  vts[maxRadiusPt].x << " " << vts[maxRadiusPt].y << " " << vts[maxRadiusPt].z <<
			" " << vts[firstEndPt].x << " " << vts[firstEndPt].y << " " << vts[firstEndPt].z <<
			" " << firstEndPt <<
			endl;**/
			//for (int i = 0; i < vts.size(); i++) {
			//	vts[i].width = 0;
			//}
		for (int i = 0; i < diameterVts.size(); i++) {
			//vts[i].stem = 1;
			vts[diameterVts[i]].stem = 1;
			//vts[diameterVts[i]].width = 1000;
			//vts[diameterVts[i]].radius = 100;
			/**std::map<int, bool> visited;
			std::queue<int> stemNeighbors;
			stemNeighbors.push(diameterVts[i]);
			while (!stemNeighbors.empty()) {
				int v = stemNeighbors.front();
				stemNeighbors.pop();
				visited[v] = true;
				vts[v].stem = 1;
				auto neighbours = adjacent_vertices(v, gOriginal);
				for (auto u : make_iterator_range(neighbours))
				{
					if (euclideanDistance(vts[diameterVts[i]], vts[u]) < vts[diameterVts[i]].radius * radiusTolerance) {
						if (visited.find(u) == visited.end()) {
							stemNeighbors.push(u);
						}
					}
				}
			}**/
			//cout << "vtx stem " << diameterVts[i] << " " << vts[diameterVts[i]].stem << " " << vts[diameterVts[i]].radius << endl;
		}

		for (int i = 0; i < vts.size(); i++) {
			if (vts[i].radius > lowerRadiiThresh) {
				vts[i].stem = 1;
				//vts[i].width = 1000;
			}
		}

		//Get largest component
		std::vector< std::vector<int> > components;
		std::vector<int> nodeToComp(vts.size());
		int n = (int)boost::connected_components(gOriginal, &nodeToComp[0]);
		std::vector<int> isCompIndex(n, -1);
		std::vector<int> compNums(n, 0);
		for (int i = 0; i < vts.size(); i++) {
			compNums[nodeToComp[i]]++;
		}
		int largestCompIndex = -1; int largestCompSize = 0;
		for (int i = 0; i < n; i++) {
			std::cout << "Component " << i << " is of size " << compNums[i] << std::endl;
			if (compNums[i] > largestCompSize) {
				largestCompIndex = i;
				largestCompSize = compNums[i];
			}
		}
		std::cout << "Largest component " << largestCompIndex << " is of size " << largestCompSize << std::endl;
		std::map<int, int> newPtIndex;
		std::vector<VertexWithMsure> newVts;
		for (int i = 0; i < vts.size(); i++) {
			if (nodeToComp[i] == largestCompIndex) {
				newPtIndex[i] = newVts.size();
				newVts.push_back(vts[i]);
			}
		}
		std::vector<internal::Edge> newEdges;
		for (int i = 0; i < edges.size(); i++) {
			if (nodeToComp[edges[i].v1] == largestCompIndex) {
				internal::Edge e;
				e.v1 = newPtIndex[edges[i].v1];
				e.v2 = newPtIndex[edges[i].v2];
				newEdges.push_back(e);
			}
		}

		ply::PLYwriter ply_writerS;
		std::map<std::string, PlyProperty> vert_propsS;
		vert_propsS["radius"] = { (char*)"radius", Float32, Float32, offsetof(VertexWithMsure, radius), PLY_SCALAR, 0, 0, 0 };
		vert_propsS["bt2"] = { (char*)"bt2", Float32, Float32, offsetof(VertexWithMsure, width), PLY_SCALAR, 0, 0, 0 };

		vert_propsS["stem"] = { (char*)"stem", Int32, Int32, offsetof(VertexWithMsure, stem), PLY_SCALAR, 0, 0, 0 };
		vert_propsS["x"] = { (char*)"x", Float32, Float32, offsetof(VertexWithMsure, x), PLY_SCALAR, 0, 0, 0 };

		vert_propsS["y"] = { (char*)"y", Float32, Float32, offsetof(VertexWithMsure, y), PLY_SCALAR, 0, 0, 0 };

		vert_propsS["z"] = { (char*)"z", Float32, Float32, offsetof(VertexWithMsure, z), PLY_SCALAR, 0, 0, 0 };



		std::map<std::string, PlyProperty> edge_propsS;

		edge_propsS["vertex1"] = { (char*)"vertex1", Int32, Int32, offsetof(ply::Edge, v1), PLY_SCALAR, 0, 0, 0 };

		edge_propsS["vertex2"] = { (char*)"vertex2", Int32, Int32, offsetof(ply::Edge, v2), PLY_SCALAR, 0, 0, 0 };

		std::map<std::string, PlyProperty> face_propsS;

		face_propsS["vertex_indices"] = {

			(char*)"vertex_indices", Int32, Int32, offsetof(ply::Face, verts),

			PLY_LIST, Uint8, Uint8, offsetof(ply::Face,nvts) };
		cout << "Written to " << outFile.c_str() << endl;
		ply_writerS.write(outFile.c_str(), true, true, true,

			vert_propsS, edge_propsS, face_propsS,

			newVts, newEdges, faces);
		return 0;
	}

	std::cout << "vts size " << vts.size() << std::endl;
	int ct = 0;
	for (int i = 0; i < vts.size(); i++) {
		vts[i].width = 0;
	}
	//for (int i = 0; i < diameterVts.size(); i++) {
		//vts[diameterVts[i]].width = 1;
	//}

	double* diameterValues = new double[diameterVts.size() * 3];
	float centerX = 0.0;
	float centerY = 0.0;
	float centerZ = 0.0;
	int lowestSeed = 0;
	for (int i = 0; i < diameterVts.size(); i++) {
		diameterValues[3 * i] = vts[diameterVts[i]].x;
		diameterValues[(3 * i) + 1] = vts[diameterVts[i]].y;
		diameterValues[(3 * i) + 2] = vts[diameterVts[i]].z;

		centerX += vts[diameterVts[i]].x;
		centerY += vts[diameterVts[i]].y;
		centerZ += vts[diameterVts[i]].z;

		if (vts[diameterVts[i]].radius > vts[lowestSeed].radius) {
			lowestSeed = diameterVts[i];
		}
	}
	centerX /= diameterVts.size();
	centerY /= diameterVts.size();
	centerZ /= diameterVts.size();
	vector<float> center = { centerX, centerY, centerZ };

	map<int, bool> origVertexInDiameter;
	vector<float> stemCentroid = { 0.0,0.0,0.0 };
	for (const auto& myPair : vertexInDiameter) {
		origVertexInDiameter[myPair.first] = true;
		stemCentroid[0] += vts[myPair.first].x;
		stemCentroid[1] += vts[myPair.first].y;
		stemCentroid[2] += vts[myPair.first].z;
	}
	stemCentroid[0] /= diameterVts.size();
	stemCentroid[1] /= diameterVts.size();
	stemCentroid[2] /= diameterVts.size();

	vector < vector<int> > vertEdgesVec;
	for (int i = 0; i < vts.size(); i++) {
		vector<int> nVec;
		vertEdgesVec.push_back(nVec);
	}
	for (const auto& myPair : vertIndexEdgeIndices) {
		vertEdgesVec[myPair.first] = myPair.second;
	}
	vector<int> lastLoop;
	map<int, bool> visited = origVertexInDiameter;
	map<int, int> branchEndToStartMapping;
	int lowestIndex = 0;
	vector< std::tuple<int, float> > junctionDistances;
	float distTotal = 0.0;
	map<int, float> junctionDistToLowestSeed;
	vector<float> seedJunctionDistances;
	float firstPrimaryBranchLength = 0.0;
	int firstBranchIndex = -1;

	vector<std::tuple<int, float> > diameterVtsTuples;
	for (int i = 0; i < diameterVts.size(); i++) {
		diameterVtsTuples.push_back(std::make_tuple(diameterVts[i], -parentDistDiam[diameterVts[i]]));
		//diameterVtsTuples.push_back(std::make_tuple(diameterVts[i], ));
	}

	sort(diameterVtsTuples.begin(), diameterVtsTuples.end(), sortbysec);

	cout << "diameterVtsTuples " << diameterVtsTuples.size() << endl;
	//sort from stem bottom to stem top
	diameterVts.clear();
	for (int i = 0; i < diameterVtsTuples.size(); i++) {
		diameterVts.push_back(get<0>(diameterVtsTuples[i]));
	}
	vector<bool> visitedVts(vts.size(), false);
	for (const auto& myPair : visited) {
		visitedVts[myPair.first] = true;
	}
	float avgTipAngle = 0.0;
	float avgEmergenceAngle = 0.0;
	float avgBranchLength = 0.0;
	std::vector<int> depthMap(vts.size(), 0);
	int maxRadiusPt = diameterVts[0];

	//Compute stem point closest to the top z slice. Geodesic depth is computed relative to firstEndPt
	float maxX = -1000; float maxY = -1000; float maxZ = -1000;
	float minX = 1000; float minY = 1000; float minZ = 1000;
	int firstEndPt = -1;
	for (int i = 0; i < diameterVts.size(); i++) {
		//vts[diameterVts[i]].width = parentDistDiam[diameterVts[i]];
		maxX = max(maxX, vts[diameterVts[i]].x);
		maxY = max(maxY, vts[diameterVts[i]].y);
		maxZ = max(maxZ, vts[diameterVts[i]].z);

		minX = min(minX, vts[diameterVts[i]].x);
		minY = min(minY, vts[diameterVts[i]].y);
		minZ = min(minZ, vts[diameterVts[i]].z);

		if (vts[diameterVts[i]].radius > vts[maxRadiusPt].radius) {
			maxRadiusPt = diameterVts[i];
		}
		if (firstEndPt == -1) {
			firstEndPt = diameterVts[i];
		}
		else {
			if (vts[diameterVts[i]].z < vts[firstEndPt].z) {
				firstEndPt = diameterVts[i];
			}
		}

	}

	std::vector< vertex_descriptor > p(num_vertices(gOriginal));
	vertex_descriptor s = vertex(firstEndPt, gOriginal);
	std::vector< float > d(num_vertices(gOriginal));
	//Find geodesic depth to all points in skeleton
	dijkstra_shortest_paths(gOriginal, s,
		predecessor_map(boost::make_iterator_property_map(
			p.begin(), get(boost::vertex_index, gOriginal)))
		.distance_map(boost::make_iterator_property_map(
			d.begin(), get(boost::vertex_index, gOriginal))));
	/**
	graph_traits< Graph >::vertex_iterator vi, vend;
	for (boost::tie(vi, vend) = vertices(gOriginal); vi != vend; ++vi)
	{
		std::cout << "distance(" << *vi << ") = " << d[*vi] << ", ";
		std::cout << "parent(" << *vi << ") = " << p[*vi]
			<< std::endl;
	}
	std::cout << std::endl;**/


	std::vector<int> stemSeeds; std::vector<int> junctions;
	for (int i = 0; i < diameterVts.size(); i++) {
		//Temporary hack assigning stem hierarchy depth to 0
		junctionDistToLowestSeed[diameterVts[i]] = distTotal;
		if (i + 1 < diameterVts.size()) {
			distTotal += euclideanDistance(vts[diameterVts[i]], vts[diameterVts[i + 1]]);
		}
		vector<int> vertEdges = vertIndexEdgeIndices[diameterVts[i]];

		if (vertEdges.size() > 2) {
			for (int j = 0; j < vertEdges.size(); j++) {
				internal::Edge edge = edges[vertEdges[j]];
				int junctionIndex = -1;
				if (edge.v1 == diameterVts[i]) {
					junctionIndex = edge.v2;
				}
				if (edge.v2 == diameterVts[i]) {
					junctionIndex = edge.v1;
				}
				if (junctionIndex != -1) {

					float length = 0.0;
					//Build primary branches from this junction
					//if (!visitedVts[junctionIndex]) {
					findStemSeeds(gOriginal, visitedVts, depthMap, diameterVts[i], junctionIndex, 0, vts, radiusTolerance, stemSeeds, junctions);

					//}
				}
			}
		}
		else {
			if (vertEdges.size() == 2) {
				for (int j = 0; j < vertEdges.size(); j++) {
					internal::Edge edge = edges[vertEdges[j]];
					int junctionIndex = -1;
					if (!visitedVts[edge.v1]) {
						junctionIndex = edge.v1;
					}
					else {
						if (!visitedVts[edge.v2]) {
							junctionIndex = edge.v2;
						}
					}
					if (junctionIndex != -1) {
						float length = 0.0;
						//Build primary branches from this junction
						//if (!visitedVts[junctionIndex]) {
						findStemSeeds(gOriginal, visitedVts, depthMap, diameterVts[i], junctionIndex, 0, vts, radiusTolerance, stemSeeds, junctions);
						//}
					}
				}
			}
		}

	}
	std::vector<Branch> branches;
	map<int, int> branchPtr;
	map<int, int> branchParent;
	for (int i = 0; i < stemSeeds.size(); i++) {
		int branchDepth = 1;
		Branch branch;
		branch.level = 1;
		branch.fork = stemSeeds[i];
		branch.length = 0.0;
		branch.tipGeodesicDepth = d[stemSeeds[i]];
		branch.parent = -1;
		branch.valid = true;
		branches.push_back(branch);
		branchPtr[stemSeeds[i]] = branches.size() - 1;
		//float length = 0.0;
		std::vector<float> dir = { vts[stemSeeds[i]].x - vts[junctions[i]].x, vts[stemSeeds[i]].y - vts[junctions[i]].y, vts[stemSeeds[i]].z - vts[junctions[i]].z };
		buildHierarchy(gOriginal, visitedVts, depthMap, stemSeeds[i], branch.level, vts, dir, branches, branches.size() - 1, branchPtr);
	}

	struct levelStat {
		float length = 0.0;
		float geodesicDepth = 0.0;
		float avgRadius = 0.0;
		int level = 0;
		int branchCount = 0;
		int edges = 0;
		float tortuosity = 0.0;
		float gravityAngle = 0.0;
		float parentAngle = 0.0;
		float tipAngle = 0.0;
		float emergenceAngle = 0.0;
		float midpointAngle = 0.0;
		float numChildren;
	};
	map<int, levelStat> levelStats;
	std::ofstream outStream;
	outStream.open(traitFile, std::ios_base::app);
	if (!outStream.is_open()) {
		std::cout << "not open" << std::endl;
		return 1;
	}

	std::sort(branches.begin(), branches.end(), compareByLevel);
	if (branch) {
		outStream << "Per-branch statistics" << endl;
		outStream << "Index, Level, Length, Geodesic depth, Average Radius, Skeleton edges, Tortuosity, Tip Location X, Tip Location Y, Tip Location Z, Number of Children, Angle to Gravity, Parent angle, Tip angle, Emergence angle, Midpoint angle" << endl;
	}
	int branchIndex = 0;
	float totalEuclid = 0.0;
	float totalNumChildren = 0.0;
	for (int i = 0; i < branches.size(); i++) {
		if (branches[i].valid && branches[i].positions.size() > 10 && branches[i].level <= maxLevel) {
			branchIndex++;
			//maxLevel = max(branches[i].level, maxLevel);
			if (branches[i].level > 1) { //For level 1 branches, already subtracted portion within stem
				branches[i].length -= vts[branches[i].fork].radius; //Subtract part of skeleton that was within stem
			}
			branches[i].avgRadius = branches[i].avgRadius / branches[i].positions.size();

			float euclideanDist = euclideanDistance(vts[branches[i].tip], vts[branches[i].fork]);
			totalEuclid += euclideanDist;

			float tortuosity = branches[i].length / euclideanDist;


			alglib::ae_int_t infoB;

			// scalar values that describe variances along each eigenvector
			alglib::real_1d_array eigValuesB;

			// unit eigenvectors which are the orthogonal basis that we want
			alglib::real_2d_array eigVectorsB;
			alglib::real_2d_array ptInputB;

			double* branchVtArr = new double[(branches[i].positions.size() + 1) * 3];
			branchVtArr[0] = (double)vts[branches[i].fork].x;
			branchVtArr[1] = (double)vts[branches[i].fork].y;
			branchVtArr[2] = (double)vts[branches[i].fork].z;
			for (int o = 0; o < branches[i].positions.size(); o++) {
				branchVtArr[3 * (o + 1)] = (double)vts[branches[i].positions[o]].x;
				branchVtArr[3 * (o + 1) + 1] = (double)vts[branches[i].positions[o]].y;
				branchVtArr[3 * (o + 1) + 2] = (double)vts[branches[i].positions[o]].z;
			}

			ptInputB.setcontent(branches[i].positions.size(), 3, branchVtArr);
			// perform the analysis
			pcabuildbasis(ptInputB, branches[i].positions.size(), 3, infoB, eigValuesB, eigVectorsB);
			// now the vectors can be accessed as follows:
			double basis0_xB = eigVectorsB[0][0];
			double basis0_yB = eigVectorsB[1][0];
			double basis0_zB = eigVectorsB[2][0];

			//double basis1_xB = eigVectorsB[0][1];
			//double basis1_yB = eigVectorsB[1][1];
			//double basis1_zB = eigVectorsB[2][1];

			//double basis2_xB = eigVectorsB[0][2];
			//double basis2_yB = eigVectorsB[1][2];
			//double basis2_zB = eigVectorsB[2][2];
			//, (float)basis1_xB , (float)basis1_yB,  (float)basis1_zB, (float)basis2_xB , (float)basis2_yB, (float)basis2_zB 
			vector<float> pca = { (float)basis0_xB , (float)basis0_yB, (float)basis0_zB };

			VertexWithMsure forkPlusPca;
			forkPlusPca.x = vts[branches[i].fork].x + pca[0];
			forkPlusPca.y = vts[branches[i].fork].y + pca[1];
			forkPlusPca.z = vts[branches[i].fork].z + pca[2];

			VertexWithMsure forkMinusPca;
			forkMinusPca.x = vts[branches[i].fork].x - pca[0];
			forkMinusPca.y = vts[branches[i].fork].y - pca[1];
			forkMinusPca.z = vts[branches[i].fork].z - pca[2];

			if (euclideanDistance(vts[branches[i].tip], forkMinusPca) < euclideanDistance(vts[branches[i].tip], forkPlusPca)) {
				for (int j = 0; j < pca.size(); j++) {
					pca[j] = -pca[j];
				}
			}
			std::vector<float> vertDirection = { 0, 0, 1 };
			float pcaAngle = (180.0 / M_PI) * angle(vertDirection, pca);
			float parentAngle;
			if (branches[i].level == 1) {
				parentAngle = pcaAngle;
			}
			else {
				alglib::ae_int_t infoP;

				// scalar values that describe variances along each eigenvector
				alglib::real_1d_array eigValuesP;

				// unit eigenvectors which are the orthogonal basis that we want
				alglib::real_2d_array eigVectorsP;
				alglib::real_2d_array ptInputP;

				double* branchVtArrP = new double[(branches[branches[i].parent].positions.size() + 1) * 3];
				branchVtArrP[0] = (double)vts[branches[branches[i].parent].fork].x;
				branchVtArrP[1] = (double)vts[branches[branches[i].parent].fork].y;
				branchVtArrP[2] = (double)vts[branches[branches[i].parent].fork].z;
				for (int o = 0; o < branches[branches[i].parent].positions.size(); o++) {
					branchVtArrP[3 * (o + 1)] = (double)vts[branches[branches[i].parent].positions[o]].x;
					branchVtArrP[3 * (o + 1) + 1] = (double)vts[branches[branches[i].parent].positions[o]].y;
					branchVtArrP[3 * (o + 1) + 2] = (double)vts[branches[branches[i].parent].positions[o]].z;
				}

				ptInputP.setcontent(branches[branches[i].parent].positions.size(), 3, branchVtArrP);
				// perform the analysis
				pcabuildbasis(ptInputP, branches[branches[i].parent].positions.size(), 3, infoP, eigValuesP, eigVectorsP);
				// now the vectors can be accessed as follows:
				double basis0_xP = eigVectorsP[0][0];
				double basis0_yP = eigVectorsP[1][0];
				double basis0_zP = eigVectorsP[2][0];

				vector<float> pcaP = { (float)basis0_xP , (float)basis0_yP, (float)basis0_zP };

				VertexWithMsure forkPlusPcaP;
				forkPlusPcaP.x = vts[branches[branches[i].parent].fork].x + pcaP[0];
				forkPlusPcaP.y = vts[branches[branches[i].parent].fork].y + pcaP[1];
				forkPlusPcaP.z = vts[branches[branches[i].parent].fork].z + pcaP[2];

				VertexWithMsure forkMinusPcaP;
				forkMinusPcaP.x = vts[branches[branches[i].parent].fork].x - pcaP[0];
				forkMinusPcaP.y = vts[branches[branches[i].parent].fork].y - pcaP[1];
				forkMinusPcaP.z = vts[branches[branches[i].parent].fork].z - pcaP[2];

				if (euclideanDistance(vts[branches[branches[i].parent].tip], forkMinusPcaP) < euclideanDistance(vts[branches[branches[i].parent].tip], forkPlusPcaP)) {
					for (int j = 0; j < pcaP.size(); j++) {
						pcaP[j] = -pcaP[j];
					}
				}
				parentAngle = (180.0 / M_PI) * angle(pcaP, pca);

			}
			std::vector<float> tipVec = { vts[branches[i].tip].x - vts[branches[i].fork].x, vts[branches[i].tip].y - vts[branches[i].fork].y , vts[branches[i].tip].z - vts[branches[i].fork].z };
			normalize(tipVec);
			float tipAngle = (180.0 / M_PI) * angle(vertDirection, tipVec);

			//Emergence angle goes 30 vts in
			int emergenceVts = min((int)branches[i].positions.size() - 1, 29);
			std::vector<float> emergenceVec = { vts[branches[i].positions[emergenceVts]].x - vts[branches[i].fork].x, vts[branches[i].positions[emergenceVts]].y - vts[branches[i].fork].y, vts[branches[i].positions[emergenceVts]].z - vts[branches[i].fork].z };
			float emergenceAngle = (180.0 / M_PI) * angle(vertDirection, emergenceVec);

			int midway = min((int)branches[i].positions.size() - 1, (int)ceil((float)branches[i].positions.size() / (float)2.0));
			std::vector<float> midVec = { vts[branches[i].positions[midway]].x - vts[branches[i].fork].x, vts[branches[i].positions[midway]].y - vts[branches[i].fork].y, vts[branches[i].positions[midway]].z - vts[branches[i].fork].z };
			float midAngle = (180.0 / M_PI) * angle(vertDirection, midVec);

			if (branch) {
				outStream << branchIndex << "," << branches[i].level << "," << branches[i].length << "," << branches[i].tipGeodesicDepth <<
					"," << branches[i].avgRadius << "," << branches[i].positions.size() << "," << tortuosity << "," <<
					vts[branches[i].tip].x << "," << vts[branches[i].tip].y << "," << vts[branches[i].tip].z << "," << branches[i].children.size() <<
					"," << pcaAngle << "," << parentAngle << "," << tipAngle << "," << emergenceAngle << "," << midAngle <<
					endl;
			}
			if (levelStats.find(branches[i].level) == levelStats.end()) {
				levelStat stat;
				stat.branchCount = 1;
				stat.length = branches[i].length;
				stat.geodesicDepth = branches[i].tipGeodesicDepth;
				stat.avgRadius = branches[i].avgRadius;
				stat.level = branches[i].level;
				stat.edges = branches[i].positions.size();
				stat.tortuosity = tortuosity;
				stat.gravityAngle = pcaAngle;
				stat.parentAngle = parentAngle;
				stat.tipAngle = tipAngle;
				stat.emergenceAngle = emergenceAngle;
				stat.midpointAngle = midAngle;
				levelStats[branches[i].level] = stat;

			}
			else {
				levelStats[branches[i].level].branchCount++;
				levelStats[branches[i].level].length += branches[i].length;
				levelStats[branches[i].level].geodesicDepth += branches[i].tipGeodesicDepth;
				levelStats[branches[i].level].avgRadius += branches[i].avgRadius;
				levelStats[branches[i].level].edges += branches[i].positions.size();
				levelStats[branches[i].level].tortuosity += tortuosity;
				levelStats[branches[i].level].gravityAngle += pcaAngle;
				levelStats[branches[i].level].parentAngle += parentAngle;
				levelStats[branches[i].level].tipAngle += tipAngle;
				levelStats[branches[i].level].emergenceAngle += emergenceAngle;
				levelStats[branches[i].level].midpointAngle += midAngle;
				levelStats[branches[i].level].numChildren += branches[i].children.size();
			}
			totalNumChildren += branches[i].children.size();
		}
	}
	//outStream << "" << endl;
	//outStream << "Per-level statistics" << endl;
	//outStream << "Branch level, Branch Count, Average Length, Average Geodesic depth, Average Radius, Total skeleton edges, Average Tortuosity, Average angle to gravity, Average angle to parent branch, Average tip angle, Average emergence angle, Average midpoint angle" << endl;
	float totalLength = 0.0;
	int totalBranches = 0;
	int totalSkelEdges = 0;
	float totalParentAngle = 0.0;
	float totalTipAngle = 0.0;
	float totalGravityAngle = 0.0;
	float totalEmergenceAngle = 0.0;
	float totalMidAngle = 0.0;
	std::vector<string> outFileStr = split(outFile, "/");
	string lastStr = outFileStr[outFileStr.size() - 1];
	std::vector<string> nameStr = split(lastStr, ".");
	string name = nameStr[0];
	outStream << name << ",";
	for (int i = 1; i <= maxLevel; i++) {
		totalLength += levelStats[i].length;
		totalBranches += levelStats[i].branchCount;
		totalSkelEdges += levelStats[i].edges;
		totalParentAngle += levelStats[i].parentAngle;
		totalGravityAngle += levelStats[i].gravityAngle;
		totalTipAngle += levelStats[i].tipAngle;
		totalEmergenceAngle += levelStats[i].emergenceAngle;
		totalMidAngle += levelStats[i].midpointAngle;

		levelStats[i].length /= levelStats[i].branchCount;
		levelStats[i].geodesicDepth /= levelStats[i].branchCount;
		levelStats[i].avgRadius /= levelStats[i].branchCount;
		levelStats[i].tortuosity /= levelStats[i].branchCount;
		levelStats[i].gravityAngle /= levelStats[i].branchCount;
		levelStats[i].parentAngle /= levelStats[i].branchCount;
		levelStats[i].tipAngle /= levelStats[i].branchCount;
		levelStats[i].emergenceAngle /= levelStats[i].branchCount;
		levelStats[i].midpointAngle /= levelStats[i].branchCount;
		levelStats[i].numChildren /= levelStats[i].branchCount;
		outStream << levelStats[i].branchCount << "," << levelStats[i].length << "," << levelStats[i].geodesicDepth
			<< "," << levelStats[i].avgRadius << "," << levelStats[i].edges << "," << levelStats[i].tortuosity
			<< "," << levelStats[i].gravityAngle << "," << levelStats[i].parentAngle << "," << levelStats[i].tipAngle << "," << levelStats[i].emergenceAngle
			<< "," << levelStats[i].midpointAngle << "," << levelStats[i].numChildren << ",";
	}
	//outStream << "Per-node statistics" << endl;
	//outStream << "Branch Count, Average Length, Average Geodesic depth, Average Radius, Total skeleton edges, Average Tortuosity, 1-Branch Count, 1-Branch Total Length, 1-Branch Avg. Length, 1-Branch Geodesic Depth, 1-Branch Average Radius, 1-Branch skeleton edges, 1-Branch Average Tortuosity, 2-Branch Count, 2-Branch Total Length, 2-Branch Avg. Length, 2-Branch Geodesic Depth, 2-Branch Average Radius, 2-Branch skeleton edges, 2-Branch Average Tortuosity, 3-Branch Count, 3-Branch Total Length, 3-Branch Avg. Length, 3-Branch Geodesic Depth, 3-Branch Average Radius, 3-Branch skeleton edges, 3-Branch Average Tortuosity, 4-Branch Count, 4-Branch Total Length, 4-Branch Avg. Length, 4-Branch Geodesic Depth, 4-Branch Average Radius, 4-Branch skeleton edges, 4-Branch Average Tortuosity, 5-Branch Count, 5-Branch Total Length, 5-Branch Avg. Length, 5-Branch Geodesic Depth, 5-Branch Average Radius, 5-Branch skeleton edges, 5-Branch Average Tortuosity, 6-Branch Count, 6-Branch Total Length, 6-Branch Avg. Length, 6-Branch Geodesic Depth, 6-Branch Average Radius, 6-Branch skeleton edges, 6-Branch Average Tortuosity" << endl;
	// "" << endl;
	//outStream << "Overall statistics" << endl;
	//outStream << "Total branch length, Number of tips (= number of branches), Average branch length, Average tortuosity, Total skeleton edges, Average angle to gravity, Average parent angle, Average tip angle, Average emergence angle, Average midpoint angle" << endl;
	//outStream <<

	outStream << totalLength << "," << totalBranches << "," << totalLength / (float)totalBranches << "," << totalLength / (float)totalEuclid << "," << totalSkelEdges << "," << totalGravityAngle / totalBranches << "," << totalParentAngle / totalBranches << "," << totalTipAngle / totalBranches << "," << totalEmergenceAngle / totalBranches << "," << totalMidAngle / totalBranches << "," << totalNumChildren / ((float)totalBranches) << endl;

	/**
	for (int i = 0; i < diameterVts.size(); i++) {
		//Temporary hack assigning stem hierarchy depth to 0
		junctionDistToLowestSeed[diameterVts[i]] = distTotal;
		if (i + 1 < diameterVts.size()) {
			distTotal += euclideanDistance(vts[diameterVts[i]], vts[diameterVts[i + 1]]);
		}
		vector<int> vertEdges = vertIndexEdgeIndices[diameterVts[i]];

		if (vertEdges.size() > 2) {
			for (int j = 0; j < vertEdges.size(); j++) {
				internal::Edge edge = edges[vertEdges[j]];
				int junctionIndex = -1;
				if (edge.v1 == diameterVts[i]) {
					junctionIndex = edge.v2;
				}
				if (edge.v2 == diameterVts[i]) {
					junctionIndex = edge.v1;
				}
				if (junctionIndex != -1) {

					float length = 0.0;
					//Build primary branches from this junction
					if (!visitedVts[junctionIndex]) {
						buildBranchesFromJunction(gOriginal, visitedVts, depthMap, diameterVts[i], junctionIndex, 1, vts, 1.5);

						//buildHierarchy(gOriginal, visitedVts, depthMap, stemToOrigVertexMapping[diameterVts[i]], junctionIndex, 1, vts, length);
					}
				}
			}
		}
		else {
			if (vertEdges.size() == 2) {
				for (int j = 0; j < vertEdges.size(); j++) {
					internal::Edge edge = edges[vertEdges[j]];
					int junctionIndex = -1;
					if (!visitedVts[edge.v1]) {
						junctionIndex = edge.v1;
					}
					else {
						if (!visitedVts[edge.v2]) {
							junctionIndex = edge.v2;
						}
					}
					if (junctionIndex != -1) {
						float length = 0.0;
						//Build primary branches from this junction
						if (!visitedVts[junctionIndex]) {
							buildBranchesFromJunction(gOriginal, visitedVts, depthMap, diameterVts[i], junctionIndex, 1, vts, 1.5);
						}
					}
				}
			}
		}

	}**/
	//Temporarily, the bt2 trait is rigged to represent the branch level, so it can be visualized in the ET software. Here I just give an actual name as well.

	for (int i = 0; i < vts.size(); i++) {
		vts[i].level = vts[i].width;
	}
	ply::PLYwriter ply_writerS;
	std::map<std::string, PlyProperty> vert_propsS;
	vert_propsS["radius"] = { (char*)"radius", Float32, Float32, offsetof(VertexWithMsure, radius), PLY_SCALAR, 0, 0, 0 };
	vert_propsS["bt2"] = { (char*)"bt2", Float32, Float32, offsetof(VertexWithMsure, width), PLY_SCALAR, 0, 0, 0 };
	vert_propsS["level"] = { (char*)"level", Int32, Int32, offsetof(VertexWithMsure, level), PLY_SCALAR, 0, 0, 0 };
	vert_propsS["x"] = { (char*)"x", Float32, Float32, offsetof(VertexWithMsure, x), PLY_SCALAR, 0, 0, 0 };

	vert_propsS["y"] = { (char*)"y", Float32, Float32, offsetof(VertexWithMsure, y), PLY_SCALAR, 0, 0, 0 };

	vert_propsS["z"] = { (char*)"z", Float32, Float32, offsetof(VertexWithMsure, z), PLY_SCALAR, 0, 0, 0 };



	std::map<std::string, PlyProperty> edge_propsS;

	edge_propsS["vertex1"] = { (char*)"vertex1", Int32, Int32, offsetof(ply::Edge, v1), PLY_SCALAR, 0, 0, 0 };

	edge_propsS["vertex2"] = { (char*)"vertex2", Int32, Int32, offsetof(ply::Edge, v2), PLY_SCALAR, 0, 0, 0 };

	std::map<std::string, PlyProperty> face_propsS;

	face_propsS["vertex_indices"] = {

		(char*)"vertex_indices", Int32, Int32, offsetof(ply::Face, verts),

		PLY_LIST, Uint8, Uint8, offsetof(ply::Face,nvts) };
	cout << "Exporting to " << outFile.c_str() << endl;
	ply_writerS.write(outFile.c_str(), true, true, true,

		vert_propsS, edge_propsS, face_propsS,

		vts, edges, faces);

	//ply_writerS.write("C:/Users/danzeng/topoData/stem.ply", true, true, true,

		//vert_propsS, edge_propsS, face_propsS,

		//stemVertices, stemEdges, stemFaces);

	std::cout << totalDistance / ((float)numEndPts) << std::endl;
	return 0;
}


