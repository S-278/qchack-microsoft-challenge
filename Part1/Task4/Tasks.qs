namespace QCHack.Task4 {
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Arrays;

    // Task 4 (12 points). f(x) = 1 if the graph edge coloring is triangle-free
    // 
    // Inputs:
    //      1) The number of vertices in the graph "V" (V ≤ 6).
    //      2) An array of E tuples of integers "edges", representing the edges of the graph (0 ≤ E ≤ V(V-1)/2).
    //         Each tuple gives the indices of the start and the end vertices of the edge.
    //         The vertices are indexed 0 through V - 1.
    //         The graph is undirected, so the order of the start and the end vertices in the edge doesn't matter.
    //      3) An array of E qubits "colorsRegister" that encodes the color assignments of the edges.
    //         Each color will be 0 or 1 (stored in 1 qubit).
    //         The colors of edges in this array are given in the same order as the edges in the "edges" array.
    //      4) A qubit "target" in an arbitrary state.
    //
    // Goal: Implement a marking oracle for function f(x) = 1 if
    //       the coloring of the edges of the given graph described by this colors assignment is triangle-free, i.e.,
    //       no triangle of edges connecting 3 vertices has all three edges in the same color.
    //
    // Example: a graph with 3 vertices and 3 edges [(0, 1), (1, 2), (2, 0)] has one triangle.
    // The result of applying the operation to state (|001⟩ + |110⟩ + |111⟩)/√3 ⊗ |0⟩ 
    // will be 1/√3|001⟩ ⊗ |1⟩ + 1/√3|110⟩ ⊗ |1⟩ + 1/√3|111⟩ ⊗ |0⟩.
    // The first two terms describe triangle-free colorings, 
    // and the last term describes a coloring where all edges of the triangle have the same color.
    //
    // In this task you are not allowed to use quantum gates that use more qubits than the number of edges in the graph,
    // unless there are 3 or less edges in the graph. For example, if the graph has 4 edges, you can only use 4-qubit gates or less.
    // You are guaranteed that in tests that have 4 or more edges in the graph the number of triangles in the graph 
    // will be strictly less than the number of edges.
    //
    // Hint: Make use of helper functions and helper operations, and avoid trying to fit the complete
    //       implementation into a single operation - it's not impossible but make your code less readable.
    //       GraphColoring kata has an example of implementing oracles for a similar task.
    //
    // Hint: Remember that you can examine the inputs and the intermediary results of your computations
    //       using Message function for classical values and DumpMachine for quantum states.
    //
    operation Task4_TriangleFreeColoringOracle (
        V : Int, 
        edges : (Int, Int)[], 
        colorsRegister : Qubit[], 
        target : Qubit
    ) : Unit is Adj+Ctl {
        let triangles = FindTriangles(edges);
        let ancillaQbs = new Qubit[Length(triangles)];
        for (triangleNum, triangle) in Enumerated(triangles) {
            let triangleIndeces = GetTriangleIndeces(triangle,edges);
            Task3_ValidTriangle([colorsRegister[triangleIndeces[0]], colorsRegister[triangleIndeces[1]], colorsRegister[triangleIndeces[2]]], ancillaQbs[triangleNum]);
        }
        
        ApplyControlledOnInt(raiseTwoToPwr(Length(ancillaQbs))-1, X, ancillaQbs, target);
    }
    internal function FindTriangles (edges : (Int,Int)[]) : ((Int,Int),(Int,Int),(Int,Int))[] {
        mutable triangles = new ((Int,Int),(Int,Int),(Int,Int))[Length(edges)]; mutable triangleCtr = 0;
        for (i,edge1) in Enumerated(edges) {
            for (j,edge2) in Enumerated(edges) {
                if (i != j and EdgesShareVertex([edge1,edge2]) != -1) {
                    for (k,edge3) in Enumerated(edges) {
                        if (i!= k and j != k and EdgesShareVertex([edge3,edge2]) != -1 and EdgesShareVertex([edge1,edge3]) != -1) {
                            set triangles w/= triangleCtr <- (edge1,edge2,edge3);
                            set triangleCtr += 1;
                        }
                    }
                }
                
            }
        }
        return triangles;
    }

    internal function EdgesShareVertex (edges : (Int,Int)[]) : Int {
        let (v0,v1) = edges[0]; let (v2,v3) = edges[1];
        if (v0 == v2 or v0 == v3) {return v0;}
        elif (v1 == v2 or v1 == v3) {return v1;}
        else {return -1;}
    }

    operation Task3_ValidTriangle (inputs : Qubit[], output : Qubit) : Unit is Adj+Ctl {
        within {
            CNOT(inputs[0],inputs[1]);
            CNOT(inputs[2],inputs[0]);
            X(inputs[0]); X(inputs[1]);
        } apply {
            X(output);
            CCNOT(inputs[0],inputs[1],output);
        }
    }
    internal function GetTriangleIndeces (triangle : ((Int,Int),(Int,Int),(Int,Int)), edges : (Int,Int)[]) : Int[] {
        let (edge1,edge2,edge3) = triangle; mutable edgeIndexes = new Int[3];
        for (i,edge) in Enumerated(edges) {
			if (TuplesAreEqual(edge,edge1)) {set edgeIndexes w/= 1 <- i;}
                elif (TuplesAreEqual(edge,edge2)) {set edgeIndexes w/= 2 <- i;}
                elif (TuplesAreEqual(edge,edge3)) {set edgeIndexes w/= 3 <- i;}
            }
            return edgeIndexes;
    }
    internal function TuplesAreEqual (tuple1 : (Int,Int), tuple2 : (Int,Int)) : Bool {
        let (v0,v1) = tuple1; let (v2,v3) = tuple2;
        return v0 == v2 and v1 == v3;
    }

    internal function raiseTwoToPwr (pwr : Int) : Int {
        if (pwr == 1) {return 2;}
        else {return 2 * raiseTwoToPwr(pwr-1);}
    }
}

