-module(test_raft_erla).

-export([main/0]).

-include_lib("stdlib/include/assert.hrl").

main() ->
  % create raft nodes
  Node1 = raft_Erla:start_process_raftNode(1),
  global:sync(),
  Node2 = raft_Erla:start_process_raftNode(2),
  global:sync(),
  Node3 = raft_Erla:start_process_raftNode(3),
  global:sync(),

  timer:sleep(5000),

  Timeouter1 = raft_Erla:start_process_timeouter(4), % send timeout to node 1 (4 mod size(numNodes))
  global:sync(),

  timer:sleep(2000),

  erla_libs_comm:register_proc(667),

  Msg1 = #{key_mtype => "ProposeMessage", key_mcmd => #{key_data => "x"}},
  erla_libs_comm:send(1, Msg1),
  timer:sleep(5000),

  Msg2 = #{key_mtype => "ProposeMessage", key_mcmd => #{key_data => "y"}},
  erla_libs_comm:send(1, Msg2),
  timer:sleep(5000),

  Msg3 = #{key_mtype => "ProposeMessage", key_mcmd => #{key_data => "z"}},
  erla_libs_comm:send(1, Msg3),
  timer:sleep(5000).