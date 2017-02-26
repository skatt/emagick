%% -----------------------------------------------------------------------------
%%
%% emagick: Wrapper for Graphics/ImageMagick command line tool.
%%
%% Copyright (c) 2012 KIVRA
%%
%% Permission is hereby granted, free of charge, to any person obtaining a
%% copy of this software and associated documentation files (the "Software"),
%% to deal in the Software without restriction, including without limitation
%% the rights to use, copy, modify, merge, publish, distribute, sublicense,
%% and/or sell copies of the Software, and to permit persons to whom the
%% Software is furnished to do so, subject to the following conditions:
%%
%% The above copyright notice and this permission notice shall be included in
%% all copies or substantial portions of the Software.
%%
%% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
%% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
%% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
%% AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
%% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
%% FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
%% DEALINGS IN THE SOFTWARE.
%% -----------------------------------------------------------------------------
-module(emagick).
-author('Per Andersson').

-export([convert/3, convert/4, convert/5, convert/6]).
-export([mogrify/2, mogrify/3]).
-export ([identify/1, identify/2, identify/3, identify/4]).
-export ([with/3, with/4, with_identify/1, with_identify/2]).
-export ([with_convert/2, with_convert/3, with_convert/4]).
-export ([with_mogrify/1,with_mogrify/2]).

-define (DEFAULT_WORKDIR, "/tmp/emagick").
-define (WORKDIR (AppEnv), proplists:get_value(working_directory, AppEnv, ?DEFAULT_WORKDIR)).
-define (MAGICK_PFX (AppEnv), proplists:get_value(magick_prefix, AppEnv, "")).
%% -----------------------------------------------------------------------------

-spec with(InData, From, Funs) -> {ok, Result}
  when InData :: binary(),
  From   :: atom(),
  Funs   :: list(function()),
  Result :: term().
-spec with(InData, From, Funs, AppEnv) -> {ok, Result}
  when InData :: binary(),
  From   :: atom(),
  Funs   :: list(function()),
  AppEnv :: proplists:proplist(),
  Result :: term().
%%
%% @doc
%%      Call functions in a session with *Magick
%% @end
%% -----------------------------------------------------------------------------
with(InData, From, Funs) -> with(InData, From, Funs, []).
with(InData, From, Funs, AppEnv) ->
  WorkDir = ?WORKDIR(AppEnv),
  ok = filelib:ensure_dir(WorkDir ++ "/"),
  Filename = uuid:uuid_to_string(uuid:get_v4()),
  InFile = WorkDir ++ "/" ++ Filename ++ "." ++ atom_to_list(From),
  ok = file:write_file(InFile, InData),
  % Res = call_funs(Funs, {InFile, AppEnv}),
  try lists:foldl(fun (Fun, Arg) -> Fun(Arg) end, {InFile, [{filename, Filename}, {from, From} | AppEnv]}, Funs) of
    Res -> Res
  catch Err -> {error, Err}
  after
    file:delete(InFile)
  end.

-spec with_identify(Args) -> {Args, Info}
  when Args   :: {InFile, AppEnv},
  InFile :: string(),
  AppEnv :: proplists:proplist(),
  Info   :: proplists:proplist().
-spec with_identify(Args, Opts) -> {Args, Info}
  when Args   :: {InFile, AppEnv},
  InFile :: string(),
  AppEnv :: proplists:proplist(),
  Opts   :: proplists:proplist(),
  Info   :: proplists:proplist().
%%
%% @doc
%%      Within a session, get the input file metadata
%% @end
%% -----------------------------------------------------------------------------
with_identify(Args) -> with_identify(Args, []).
with_identify({InFile, AppEnv}, Opts) ->
  {ok, Res} = run_with(identify, [
    {infile, InFile},
    {opts, Opts},
    {app, AppEnv}]),
  {{InFile, AppEnv}, Res}.

-spec with_convert(Args, To) -> {Args, Result}
  when Args   :: {InFile, AppEnv},
  InFile :: string(),
  AppEnv :: proplists:proplist(),
  To     :: atom(),
  Result :: list(binary()).
-spec with_convert(Args, To, Opts) -> {Args, Result}
  when Args   :: {InFile, AppEnv},
  InFile :: string(),
  AppEnv :: proplists:proplist(),
  To     :: atom(),
  Opts   :: proplists:proplist(),
  Result :: list(binary()).
-spec with_convert(Args, To, Opts, ToOpts) -> {Args, Result}
  when Args   :: {InFile, AppEnv},
  InFile :: string(),
  AppEnv :: proplists:proplist(),
  To     :: atom(),
  Opts   :: proplists:proplist(),
  ToOpts   :: proplists:proplist(),
  Result :: list(binary()).
%%
%% @doc
%%      Within a session, convert the input file with *Magick.
%% @end
%% -----------------------------------------------------------------------------
with_convert(Args, To) -> with_convert(Args, To, [], []).
with_convert({InFile, AppEnv}, To, Opts) -> with_convert({InFile, AppEnv}, To, Opts, []).
with_convert({InFile, AppEnv}, To, Opts, ToOpts) ->
  {ok, Res} = run_with(convert, [{infile, InFile},
    {to, To},
    {opts, Opts},
    {toopts, ToOpts},
    {app, AppEnv}]),
  {{InFile, AppEnv}, Res}.

-spec with_mogrify(Args) -> {Args, Result}
  when Args   :: {InFile, AppEnv},
  InFile :: string(),
  AppEnv :: proplists:proplist(),
  Result :: list(binary()).
-spec with_mogrify(Args, Opts) -> {Args, Result}
  when Args   :: {InFile, AppEnv},
  InFile :: string(),
  AppEnv :: proplists:proplist(),
  Opts   :: proplists:proplist(),
  Result :: list(binary()).
%%
%% @doc
%%      Within a session, mogrify the input file with *Magick.
%% @end
%% -----------------------------------------------------------------------------
with_mogrify(Args) -> with_mogrify(Args, []).
with_mogrify({InFile, AppEnv}, Opts) ->
  {ok, Res} = run_with(mogrify, [{infile, InFile},
    {opts, Opts},
    {app, AppEnv}]),
  {{InFile, AppEnv}, Res}.

-spec convert(InData, From, To) -> {ok, OutData}
  when InData  :: binary(),
  From    :: atom(), %% pdf | png | jpg | gif | ...
  To      :: atom(), %% same as To
  OutData :: binary().
-spec convert(InData, From, To, Opts) -> {ok, OutData}
  when InData  :: binary(),
  From    :: atom(),
  To      :: atom(),
  Opts    :: proplists:proplist(),
  OutData :: binary().
-spec convert(InData, From, To, Opts, AppEnv) -> {ok, OutData}
  when InData  :: binary(),
  From    :: atom(),
  To      :: atom(),
  Opts    :: proplists:proplist(),
  AppEnv  :: proplists:proplist(),
  OutData :: binary().
-spec convert(InData, From, To, Opts, AppEnv, ToOpts) -> {ok, OutData}
  when InData  :: binary(),
  From    :: atom(),
  To      :: atom(),
  Opts    :: proplists:proplist(),
  ToOpts  :: proplists:proplist(),
  AppEnv  :: proplists:proplist(),
  OutData :: binary().
%%
%% @doc
%%      Convert indata with *Magick.
%% @end
%% -----------------------------------------------------------------------------
convert(InData, From, To) -> convert(InData, From, To, []).
convert(InData, From, To, Opts) -> convert(InData, From, To, Opts, []).
convert(InData, From, To, Opts, AppEnv) -> convert(InData, From, To, Opts, AppEnv, []).
convert(InData, From, To, Opts, AppEnv, ToOpts) ->
  CB = fun (Args) -> with_convert(Args, To, Opts, ToOpts) end,
  {_, Converted} = with(InData, From, [CB], AppEnv),
  {ok, Converted}.

-spec mogrify(InData, Opts) -> {ok, OutData}
  when InData  :: binary(),
  Opts    :: proplists:proplist(),
  OutData :: binary().
-spec mogrify(InData, Opts, AppEnv) -> {ok, OutData}
  when InData  :: binary(),
  Opts    :: proplists:proplist(),
  AppEnv  :: proplists:proplist(),
  OutData :: binary().
%%
%% @doc
%%      Mogrify indata with *Magick.
%% @end
%% -----------------------------------------------------------------------------
mogrify(InData, Opts) -> mogrify(InData, Opts, []).
mogrify(InData, Opts, AppEnv) ->
  [_|Ext] = filename:extension(InData),
  CB = fun (Args) -> with_mogrify(Args, Opts) end,
  {_, Converted} = with(InData, to_atom(Ext), [CB], AppEnv),
  {ok, Converted}.


%%
%% @doc
%%      Get indata info with *Magick.
%% @end
%% -----------------------------------------------------------------------------
-spec identify(InData) -> {ok, proplists:proplist()}
  when InData :: binary().
-spec identify(InData, From) -> {ok, proplists:proplist()}
  when InData :: binary(),
  From :: atom().
-spec identify(InData, From, Opts) -> {ok, proplists:proplist()}
  when InData :: binary(),
  From :: atom(),
  Opts   :: proplists:proplist().
-spec identify(InData, From, Opts, AppEnv) -> {ok, proplists:proplist()}
  when InData :: binary(),
  From :: atom(),
  Opts   :: proplists:proplist(),
  AppEnv :: proplists:proplist().
identify(InData) -> identify(InData, xxx, []).
identify(InData, From) -> identify(InData, From, []).
identify(InData, From, Opts) -> identify(InData, From, Opts, []).
identify(InData, From, Opts, AppEnv) ->
  CB = fun (Args) -> with_identify(Args, Opts) end,
  {_, Info} = with(InData, From, [CB], AppEnv),
  {ok, [Info]}.

%% =============================================================================
%%
%% INTERNAL FUNCTIONS
%%
%% =============================================================================

%% -----------------------------------------------------------------------------
%%
%% @doc
%%      Format and execute the supplied *magick command in a 'session'.
%% @end
%% -----------------------------------------------------------------------------
% -spec run_with(Command, Opts) -> {ok, Result}
%     when Command :: atom(),
%          Opts    :: proplists:proplist(),
%          Result  :: {ok, list(binary())} | {ok, proplists:proplist()}.
-spec run_with(identify, proplists:proplist()) -> {ok, proplists:proplist()};
    (convert, proplists:proplist()) -> {ok, list(binary())};
    (mogrify, proplists:proplist()) -> {ok, list(binary())}.
run_with(identify, Opts) ->
  InFile = proplists:get_value(infile, Opts),
  CmdOpts = proplists:get_value(opts, Opts, ""),
  AppEnv = proplists:get_value(app, Opts, []),
  MagickPrefix = ?MAGICK_PFX(AppEnv),

  PortCommand = string:join([MagickPrefix, "identify", format_opts(CmdOpts), InFile], " "),
  error_logger:info_msg("emagick:identify (~s)~n",[PortCommand]),
  PortOpts = [stream, use_stdio, exit_status, binary],
  Port = erlang:open_port({spawn, PortCommand}, PortOpts),

  {ok, Data, 0} = receive_until_exit(Port, []),
  case erlang:port_info(Port) of
    undefined -> ok;
    _         -> true = erlang:port_close(Port)
  end,

  [_, Fmt, Dims | _] = binary:split(Data, <<" ">>, [trim, global]),
  [W,H] = lists:map(fun(X) -> list_to_integer(lists:takewhile(fun(C) -> C =/= $+ end,binary_to_list(X))) end, binary:split(Dims, <<"x">>)),
  {ok, [{format, Fmt},
    {dimensions, {W, H}}]};
run_with(mogrify, Opts) ->
  InFile = proplists:get_value(infile, Opts),
  %To = proplists:get_value(to, Opts),
  CmdOpts = proplists:get_value(opts, Opts, ""),
  %ToOpts = proplists:get_value(toopts, Opts, ""),
  AppEnv = proplists:get_value(app, Opts, []),

  Filename = proplists:get_value(filename, AppEnv),
  Workdir = ?WORKDIR(AppEnv),

  MagickPrefix = ?MAGICK_PFX(AppEnv),
  %OutFile = Workdir ++ "/" ++ Filename ++ "_%06d" ++ "." ++ atom_to_list(To),
  PortCommand = string:join([MagickPrefix, "mogrify",
    format_opts(CmdOpts), InFile], " "),
  error_logger:info_msg("emagick:~p (~s)~n",[mogrify,PortCommand]),
  %% execute as port
  PortOpts = [stream, use_stdio, exit_status, binary],
  Port = erlang:open_port({spawn, PortCommand}, PortOpts),

  %% crash upon non-zero exit status
  {ok, _Data, 0} = receive_until_exit(Port, []),
  case erlang:port_info(Port) of
    undefined -> ok;
    _ ->         true = erlang:port_close(Port)
  end,

  [_|Ext] = filename:extension(InFile),
  %% return converted file(s)
  {ok, _} = read_converted_files(Workdir, Filename, atom_to_list(Ext), InFile);
run_with(Fun, Opts) ->
  InFile = proplists:get_value(infile, Opts),
  To = proplists:get_value(to, Opts),
  CmdOpts = proplists:get_value(opts, Opts, ""),
  ToOpts = proplists:get_value(toopts, Opts, ""),
  AppEnv = proplists:get_value(app, Opts, []),

  Filename = proplists:get_value(filename, AppEnv),
  Workdir = ?WORKDIR(AppEnv),

  MagickPrefix = ?MAGICK_PFX(AppEnv),
  OutFile = Workdir ++ "/" ++ Filename ++ "_%06d" ++ "." ++ atom_to_list(To),
  PortCommand = string:join([MagickPrefix, to_list(Fun),
    format_opts(CmdOpts), InFile, format_toopts(ToOpts), OutFile], " "),
  error_logger:info_msg("emagick:~p (~s)~n",[Fun,PortCommand]),
  %% execute as port
  PortOpts = [stream, use_stdio, exit_status, binary],
  Port = erlang:open_port({spawn, PortCommand}, PortOpts),

  %% crash upon non-zero exit status
  {ok, _Data, 0} = receive_until_exit(Port, []),
  case erlang:port_info(Port) of
    undefined -> ok;
    _ ->         true = erlang:port_close(Port)
  end,

  %% return converted file(s)
  {ok, _} = read_converted_files(Workdir, Filename, To, InFile).

%% -----------------------------------------------------------------------------
-spec read_converted_files(Workdir, Filename, Suffix, Except) -> {ok, Result}
  when Workdir  :: string(),
  Filename :: string(),
  Suffix :: atom(),
  Except :: string(),
  Result   :: list(binary()).
%% @doc
%%      Read converted files, delete them, and return file data.
%% @end
%% -----------------------------------------------------------------------------
read_converted_files(Workdir, Filename, Suffix, Except) ->
  Files0 = filelib:wildcard(Workdir ++ "/" ++ Filename ++ "*." ++
    atom_to_list(Suffix)),
  Files = Files0 -- [Except],
  do_read_converted_files(lists:sort(Files), []).

do_read_converted_files([], Acc) ->
  {ok, lists:reverse(Acc)};
do_read_converted_files([File|Files], Acc) ->
  {ok, FileBin} = file:read_file(File),
  file:delete(File),
  do_read_converted_files(Files, [FileBin|Acc]).


%% -----------------------------------------------------------------------------
-spec format_opts(Opts) -> Result
  when Opts   :: proplists:proplist(),
  Result :: string().
%%
%% @doc
%%      Format option proplist as string.
%% @end
%% -----------------------------------------------------------------------------
format_opts(Opts) -> format_opts(Opts, []).
format_opts([], Res) -> string:join(Res, " ");
format_opts([Opt|Opts], Res) ->
  ArgStr =
    "-" ++ string:join([to_string(Arg) || Arg <- tuple_to_list(Opt)], " "),
  format_opts(Opts, Res ++ [ArgStr]).

format_toopts(Opts) -> format_toopts(Opts, []).
format_toopts([], Res) -> string:join(Res, " ");
format_toopts([Opt|Opts], Res) ->
  ArgStr =
    "+" ++ string:join([to_string(Arg) || Arg <- tuple_to_list(Opt)], " "),
  format_toopts(Opts, Res ++ [ArgStr]).

-spec to_string(term()) -> string().
to_string(E) when is_atom(E) ->    atom_to_list(E);
to_string(E) when is_binary(E) ->  binary_to_list(E);
to_string(E) when is_integer(E) -> integer_to_list(E);
to_string(E) when is_list(E) ->    E.


%% -----------------------------------------------------------------------------
-spec receive_until_exit(Port, ReverseBuffer) -> {ok, Data, Status}
  when Port          :: port(),
  ReverseBuffer :: list(iolist()),
  Data          :: binary(),
  Status        :: non_neg_integer().
%%
%% @doc
%%      Receives until the given port exits.
%% @end
%% -----------------------------------------------------------------------------
receive_until_exit(Port, ReverseBuffer) ->
  receive
    {Port, {exit_status, Status}} ->
      Data = iolist_to_binary(lists:reverse(ReverseBuffer)),
      {ok, Data, Status};
    {Port, {data, Data}} ->
      receive_until_exit(Port, [Data | ReverseBuffer])
  end.

-define(IS_STRING(Term), (is_list(Term) andalso Term /= [] andalso is_integer(hd(Term)))).

to_list(L) when ?IS_STRING(L) -> L;
to_list(L) when is_list(L) -> SubLists = [inner_to_list(X) || X <- L], lists:flatten(SubLists);
to_list(A) -> inner_to_list(A).
inner_to_list(A) when is_atom(A) -> atom_to_list(A);
inner_to_list(B) when is_binary(B) -> binary_to_list(B);
inner_to_list(I) when is_integer(I) -> integer_to_list(I);
inner_to_list(L) when is_tuple(L) -> lists:flatten(io_lib:format("~p", [L]));
inner_to_list(L) when is_list(L) -> L;
inner_to_list(F) when is_float(F) -> float_to_list(F,[{decimals,9},compact]).

to_atom(A) when is_atom(A) -> A;
to_atom(B) when is_binary(B) -> to_atom(binary_to_list(B));
to_atom(I) when is_integer(I) -> to_atom(integer_to_list(I));
to_atom(F) when is_float(F) -> to_atom(float_to_list(F,[{decimals,9},compact]));
to_atom(L) when is_list(L) -> list_to_atom(binary_to_list(list_to_binary(L))).

to_binary(A) when is_atom(A) -> atom_to_binary(A,latin1);
to_binary(B) when is_binary(B) -> B;
to_binary(T) when is_tuple(T) -> term_to_binary(T);
to_binary(I) when is_integer(I) -> to_binary(integer_to_list(I));
to_binary(F) when is_float(F) -> float_to_binary(F,[{decimals,9},compact]);
to_binary(L) when is_list(L) ->  iolist_to_binary(L).

to_integer(A) when is_atom(A) -> to_integer(atom_to_list(A));
to_integer(B) when is_binary(B) -> to_integer(binary_to_list(B));
to_integer(I) when is_integer(I) -> I;
to_integer([]) -> 0;
to_integer(L) when is_list(L) -> list_to_integer(L);
to_integer(F) when is_float(F) -> round(F).