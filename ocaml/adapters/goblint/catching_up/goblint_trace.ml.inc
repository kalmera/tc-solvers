    type trace_output = {
      channel : out_channel;
      mutable sequence : int;
      evaluation_counts : (int, int) Stdlib.Hashtbl.t;
      mutable evaluations : int;
      mutable gets : int;
      mutable sides : int;
    }

    type trace =
      | TraceDisabled
      | TraceEnabled of trace_output

    let trace_write channel json =
      Yojson.Safe.to_channel channel json;
      Stdlib.output_char channel '\n'

    let create_trace () =
      if not trace_supported then TraceDisabled
      else
        match Stdlib.Sys.getenv_opt "QSOLVER_TRACE" with
        | None | Some "" -> TraceDisabled
        | Some path ->
          let channel = Stdlib.open_out path in
          trace_write channel
            (`Assoc
               [ "type", `String "header";
                 "format", `String "qsolver-trace";
                 "version", `Int 3;
                 "algorithm", `String trace_algorithm;
                 "control", `String trace_control ]);
          TraceEnabled
            {
              channel;
              sequence = 0;
              evaluation_counts = Stdlib.Hashtbl.create 128;
              evaluations = 0;
              gets = 0;
              sides = 0;
            }

    let[@inline always] trace_emit trace event fields =
      match trace with
      | TraceDisabled -> ()
      | TraceEnabled output ->
        let sequence = output.sequence in
        output.sequence <- sequence + 1;
        trace_write output.channel
          (`Assoc
             (("type", `String event) ::
              ("seq", `Int sequence) ::
              fields));
        if sequence land 255 = 255 then Stdlib.flush output.channel

    let[@inline always] trace_node trace rank variable =
      match trace with
      | TraceDisabled -> ()
      | TraceEnabled output ->
        Stdlib.Hashtbl.add output.evaluation_counts rank 0;
        let label =
          try GobPretty.sprintf "%a" S.Var.pretty_trace variable
          with _ -> S.Var.var_id variable
        in
        trace_emit trace "node"
          [ "rank", `Int rank;
            "rhs", `Bool (Option.is_some (S.system variable));
            "label", `String label ]

    let[@inline always] trace_queue trace action rank =
      match trace with
      | TraceDisabled -> ()
      | TraceEnabled _ ->
        trace_emit trace "queue"
          [ "action", `String action;
            "rank", `Int rank ]

    let[@inline always] trace_evaluation trace rank =
      match trace with
      | TraceDisabled -> ()
      | TraceEnabled output ->
        let count =
          match Stdlib.Hashtbl.find_opt output.evaluation_counts rank with
          | Some previous -> previous + 1
          | None -> 1
        in
        Stdlib.Hashtbl.replace output.evaluation_counts rank count;
        output.evaluations <- output.evaluations + 1;
        trace_emit trace "eval"
          [ "rank", `Int rank;
            "count", `Int count ]

    let[@inline always] trace_value trace rank changed =
      match trace with
      | TraceDisabled -> ()
      | TraceEnabled _ ->
        trace_emit trace "value"
          [ "rank", `Int rank;
            "changed", `Bool changed ]

    let[@inline always] trace_dependency
        trace event source target selected_rank new_w =
      match trace with
      | TraceDisabled -> ()
      | TraceEnabled output ->
        if event = "get"
        then output.gets <- output.gets + 1
        else output.sides <- output.sides + 1;
        trace_emit trace event
          [ "source", `Int source;
            "target", `Int target;
            "selects_w", `Bool (Option.is_some selected_rank);
            "w_rank", (match selected_rank with
               | Some rank -> `Int rank
               | None -> `Null);
            "new_w", `Bool new_w ]

    let trace_finish trace nodes w =
      match trace with
      | TraceDisabled -> ()
      | TraceEnabled output ->
        trace_emit trace "finish"
          [ "nodes", `Int nodes;
            "w", `Int w;
            "evals", `Int output.evaluations;
            "gets", `Int output.gets;
            "sides", `Int output.sides ];
        Stdlib.flush output.channel;
        Stdlib.close_out output.channel
