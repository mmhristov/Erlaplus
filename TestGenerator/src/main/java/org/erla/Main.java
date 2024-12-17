package org.erla;

import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.nio.Attribute;
import org.jgrapht.nio.dot.DOTImporter;
import org.jgrapht.util.SupplierUtil;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

import static org.erla.Params.*;

public class Main {
    static HashSet<ArrayList<Util.MsgPair>> tests = new HashSet<>();

    static Set<DefaultEdge> visitedEdges = new HashSet<>();

    static Map<String, TLCErlaState> erlaStates;

    public static void main(String[] args) throws IOException {
        if (!parseArgs(args)) {
            return; // exit if arguments could not be parsed/are missing.
        }

        /*
            Import graph
         */
        DOTImporter<String, DefaultEdge> importer = new DOTImporter<>();

        Map<String, Map<String, Attribute>> attrs = new HashMap<>();
        importer.addVertexAttributeConsumer((p, a) -> {
            Map<String, Attribute> map = attrs.computeIfAbsent(p.getFirst(), k -> new HashMap<>());
            map.put(p.getSecond(), a);
        });

        Graph<String, DefaultEdge> graph = new DefaultDirectedGraph<>(SupplierUtil.createStringSupplier(), SupplierUtil.DEFAULT_EDGE_SUPPLIER, false);

        importer.setVertexFactory(label -> label);
        importer.importGraph(graph, new FileInputStream(Params.graphFile));

        // get first (initial) state
        Iterator<String> iterator = graph.vertexSet().iterator();
        String firstVertexId = null;
        if (iterator.hasNext()) {
            firstVertexId = iterator.next();
        }
        assert(firstVertexId != null);

        /*
            Parse labels and create internal state representations
         */

        Map<String, Map<String, String>> attributes = attrs.entrySet()
                .stream()
                .collect(Collectors.toMap(Map.Entry::getKey,
                        e -> e.getValue().entrySet().stream().
                                collect(Collectors.toMap(Map.Entry::getKey, e2 -> e2.getValue().getValue()))));

        erlaStates = new TLCErlaStateFactory(graph.vertexSet(), attributes).getStates();

        /*
            Traverse graph and derive tests
         */

        ArrayList<Util.MsgPair> initPath = new ArrayList<>();

        traverse(firstVertexId, initPath, graph, 0);

        /*
            Write tests to file
         */

        writeTestFile();
    }

    private static boolean parseArgs(String[] args) {
        if (args.length < 2) {
            System.out.println("Please provide a graph file as argument using \"-graph my_graph.dot\"."); // todo: show help text here
            return false;
        }

        for (int i = 1; i < args.length; i+=2) {
            String option = args[i - 1];
            String value = args[i];
            if (option.equals(GRAPH_FILE_OPTION)) {
                Params.graphFile = value;
            } else if (option.equals(TEST_DEPTH)) {
                Params.testDepth = Integer.parseInt(value);
            } else {
                System.out.println("Unknown argument \"" + option + "\""); // todo: show help text
                return false;
            }
        }

        return true;
    }

    private static void traverse(String stateId, ArrayList<Util.MsgPair> test, Graph<String, DefaultEdge> graph, int currDepth) {
        TLCErlaState currState = erlaStates.get(stateId);
        graph.removeAllEdges(stateId, stateId); // remove self loops
        Set<DefaultEdge> outgoingEdges = graph.outgoingEdgesOf(stateId);
        if (allOutEdgeVisited(outgoingEdges) || currDepth > testDepth) {
            if (!test.isEmpty()) {
                tests.add(test);
            }
            return;
        }

        for (DefaultEdge edge : outgoingEdges) {
            String succ = graph.getEdgeTarget(edge);
            if (succ.equals(stateId)) {
                continue; // skip self loops
            }
            if (!visitedEdges.contains(edge)) {
                visitedEdges.add(edge);
                TLCErlaState succState = erlaStates.get(succ);
                Util.MsgPair msg = TLCErlaState.getNewMsg(currState, succState);
                if (msg != null) {
                    test.add(msg);
                    currDepth++;
                }
                traverse(succ, new ArrayList<>(test), graph, currDepth);
            }
        }
    }

    private static boolean allOutEdgeVisited(Set<DefaultEdge> outgoingEdges) {
        return visitedEdges.containsAll(outgoingEdges);
    }

    private static void writeTestFile() throws IOException {
        try (BufferedWriter out = new BufferedWriter(new FileWriter("erla.tests"))) {
            for (ArrayList<Util.MsgPair> test : tests) {
                String line = "{[";
                line += test.stream().map(Util.MsgPair::toString).collect(Collectors.joining(", "));
                line += "]}.";
                out.write(line);
                out.newLine();
            }
        } catch (IOException e) {
            throw new IOException("Error while writing the test file: " + e);
        }
    }
}