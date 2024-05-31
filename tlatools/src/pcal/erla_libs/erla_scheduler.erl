-module(erla_scheduler).

-behaviour(gen_server).

-export([start_link/1]).
-export([schedule/2, init/1, handle_call/3, handle_cast/2, handle_info/2, terminate/2,
    code_change/3]).

-define(SERVER, ?MODULE).

-record(state, {
    test = [],
    receivedMsgs = []
}).

%%%===================================================================
%%% API
%%%===================================================================

schedule(Dest, Msg) ->
    gen_server:cast({global, ?MODULE}, {Dest, Msg}).

%%%===================================================================
%%% Spawning and gen_server implementation
%%%===================================================================

start_link(Test) ->
    gen_server:start_link({global, ?MODULE}, ?MODULE, [Test], []).

init([Test]) ->
    {ok, #state{test = Test}}.

handle_call({Dest, Msg}, _From, State = #state{}) ->
    {reply, ok, State}.

handle_cast({Dest, Msg}, State = #state{}) ->
    {NewReceivedMsgs, NewTestSequence} = processMessages([{Dest, Msg} | State#state.receivedMsgs], State#state.test),
    case NewTestSequence of
        [] -> {stop, normal, State}; % terminate once all messages in test have been scheduled
        _ -> {noreply, State#state{test = NewTestSequence, receivedMsgs = NewReceivedMsgs}}
    end.

handle_info(_Info, State = #state{}) ->
    {noreply, State}.

terminate(_Reason, _State = #state{}) ->
    ok.

code_change(_OldVsn, State = #state{}, _Extra) ->
    {ok, State}.

%%%===================================================================
%%% Internal functions
%%%===================================================================

%% Sends all received messages in the order imposed by the test sequence.

processMessages(_, []) ->
    {[], []};

processMessages(ReceivedMessages, TestSequence) ->
    CurrentMessage = hd(TestSequence),
    case lists:member(CurrentMessage, ReceivedMessages) of
        true ->
            % next message has already been received -> forward message
            NewReceivedMessages = lists:delete(CurrentMessage, ReceivedMessages),
            {Dest, Payload} = CurrentMessage,
            erlang:display(io:format("Sending message ~p to process ~p", [Payload, Dest])),
            global:send(erla_libs_comm:get_proc_name(Dest), Payload),
            processMessages(NewReceivedMessages, tl(TestSequence));
        false ->
            % next message has not been received yet
            {ReceivedMessages, TestSequence} % next message not received yet
    end.