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
#include <algorithm>

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
	float x, y, z;
	float compType;
	int inDiameter;

};


float euclideanDistance(VertexWithMsure v1, VertexWithMsure v2) {
	return sqrtf((v1.x - v2.x) * (v1.x - v2.x) + (v1.y - v2.y) * (v1.y - v2.y) + (v1.z - v2.z) * (v1.z - v2.z));
}



int main(int argc, char** argv)
{

	std::map<std::string, PlyProperty> v_props_map;
	char* inFile = NULL;
	string outFile;
	for (int i = 0; i < argc - 1; i++) {
		if (((string)argv[i]).substr(0, 2) == "--") {
			string arg = (string)argv[i];
			arg.erase(0, 2);
			if (arg == "in") {
				inFile = argv[i + 1]; //Input skeleton file: don't need in panel since the input skeleton will already be preloaded 
			}
		}
	}

	PlyProperty v_props[] = {
		{ (char*)"bt2", Float32, Float32, offsetof(VertexWithMsure, width), 0, 0, 0, 0 },
	{ (char*)"radius", Float32, Float32, offsetof(VertexWithMsure, radius), 0, 0, 0, 0 },
	//{ (char*)"bt1", Float32, Float32, offsetof(VertexWithMsure, bt1), 0, 0, 0, 0 },
	{ (char*)"x", Float32, Float32, offsetof(VertexWithMsure, x), 0, 0, 0, 0 },
	{ (char*)"y", Float32, Float32, offsetof(VertexWithMsure, y), 0, 0, 0, 0 },
	{ (char*)"z", Float32, Float32, offsetof(VertexWithMsure, z), 0, 0, 0, 0 }
	};
	v_props_map["bt2"] = v_props[0];
	v_props_map["radius"] = v_props[1];
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

	int numEndPts = 0;
	for (int i = 0; i < vts.size(); i++) {
		if (vertIndexEdgeIndices[i].size() == 1) {
			numEndPts++;
		}
	}

	std::cout << totalDistance / ((float)numEndPts) << std::endl;

	return 0;
}



