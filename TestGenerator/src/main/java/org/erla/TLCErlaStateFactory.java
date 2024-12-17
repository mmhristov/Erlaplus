package org.erla;


import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class TLCErlaStateFactory {
    /**
        The set of the graph's vertex' IDs.
     */
    Set<String> vertexIds;
    /**
        A mapping of vertex IDs to attributes. Attributes are a mapping of attribute names to attribute values.
     */
    Map<String, Map<String, String>> attributes;

    private static final Pattern pattern = Pattern.compile("^.*?(queues = \\((\\d*) :> (.*?) (?:@@ (\\d*) :> (.*?))*\\)).*$");
    private static final Pattern pattern2 = Pattern.compile("<<(.*)>>|\\{.*}|[.*]|[\\p{Alnum}\"]*");
//            Pattern.compile("^<<(.*?)(?:, (.*?))*>>$|");
        
    public TLCErlaStateFactory(Set<String> vertexIds, Map<String, Map<String, String>> attributes) {
        this.vertexIds = vertexIds;
        this.attributes = attributes;
    }

    public Map<String, TLCErlaState> getStates() {
        List<TLCErlaState> result = new ArrayList<>();

        Iterator<String> iterator = vertexIds.iterator();
        String vertexId;
        while (iterator.hasNext()) {
            vertexId = iterator.next();
            result.add(createState(vertexId));
        }

        return result.stream().collect(Collectors.toMap(TLCErlaState::getId, Function.identity()));
    }

    private TLCErlaState createState(String id) {
        String matchInput = attributes.get(id).get("label");
        Matcher matcher = pattern.matcher(matchInput);
//        Matcher matcher = pattern.matcher("queues = (0 :> <<\"hi\", \"hallo\">>, 2 :> <<>>)"); // test

        if (!matcher.find()) throw new IllegalStateException("Cannot match label \"" + matchInput + "\"");

        Map<String, String> parsedQueues = new HashMap<>();

        // Skip first two elements: first element is the whole matched string and second contains the assignment of the queue
        for (int i = 2; i <= matcher.groupCount() - 1; i+=2) {
            parsedQueues.put(matcher.group(i), matcher.group(i + 1));
        }

        Map<String, List<String>> res = parsedQueues.entrySet().stream().collect(Collectors.toMap(Map.Entry::getKey, e -> queueStrToList(e.getValue())));
        return new TLCErlaState(id, res);
    }

    private List<String> queueStrToList(String queue) {
        Matcher matcher = pattern2.matcher(queue);

        if (!matcher.find()) throw new IllegalStateException("Cannot match queue value \"" + queue + "\"");
        ArrayList<String> res = new ArrayList<>();
        // skip first element as it is the whole regex
        for (int i = 1; i <= matcher.groupCount(); i++) {
            res.add(matcher.group(i));
        }
        return res.stream().filter(Predicate.not(String::isEmpty)).collect(Collectors.toList()); // filter out empty values
    }
}
