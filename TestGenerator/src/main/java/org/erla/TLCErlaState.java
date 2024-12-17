package org.erla;

import java.util.List;
import java.util.Map;

public class TLCErlaState {

    private final String id;

    /**
     * A mapping of process IDs to values to PlusCal values.
     *  This describes the values of the processes' mailboxes in the state.
     */
    private final Map<String, List<String>> queuesValue;

    public TLCErlaState(String id, Map<String, List<String>> queuesValue) {
        this.id = id;
        this.queuesValue = queuesValue;
    }

    public String getId() {
        return id;
    }

    public static Util.MsgPair getNewMsg(TLCErlaState currentState, TLCErlaState nextState) {
        Map<String, List<String>> currentQueues = currentState.queuesValue;
        Map<String, List<String>> nextQueues = nextState.queuesValue;

        if (currentQueues.size() != nextQueues.size()) {
            throw new IllegalStateException("Queues have different sizes"); // should never happen
        }

        for (String key : currentQueues.keySet()) {
            List<String> currentQueue = currentQueues.get(key);
            List<String> nextQueue = nextQueues.get(key);
            if (nextQueue.size() > currentQueue.size()) {
                // plausibility check
                if (!nextQueue.subList(0, Integer.max(nextQueue.size() - 1, 0)).equals(currentQueue)) {
                    throw new IllegalStateException("More than one message was sent in one step");
                }
                // return new message
                return new Util.MsgPair(key, nextQueue.get(nextQueue.size() - 1));
            }
        }
        return null;
    }
}
