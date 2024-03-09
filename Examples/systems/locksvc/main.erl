-module(main).
-export([main/0]).
-import(locksvc, [start_process_Server/1, start_process_Client/1]).

main() ->
  Server = locksvc:start_process_Server(0),
  global:sync(),
  Client1 = locksvc:start_process_Client(1),
  global:sync(),
  Client2 = locksvc:start_process_Client(2).
