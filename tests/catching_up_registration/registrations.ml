let () =
  assert (not Slrtc_catching_up_register.Features.dead_side_elimination);
  assert (List.length !Selector.names = 13);
  assert (List.mem "slrtc_dfr_no_side_reset_keep_dead_default" !Selector.names);
  assert (List.mem "slrtc_plus_restarting_no_side_reset_keep_dead_default" !Selector.names);
  assert (List.mem "slrtc_dfr_no_side_reset_keep_dead_default_immediate" !Selector.names);
  assert (List.mem "slrtc_plus_restarting_no_side_reset_keep_dead_default_immediate" !Selector.names);
  assert (List.mem "slrtc_dfs_default" !Selector.names);
  assert (List.mem "slrtc_dfs_default_immediate" !Selector.names);
  assert (not Slrtc_catching_up_register.Fifo.recompute_controlled);
  assert (Slrtc_catching_up_register.FifoRecompute.recompute_controlled);
  assert (List.mem "slrtc_dfr_no_side_reset_keep_dead_default_recompute_controlled" !Selector.names);
  assert (List.mem "slrtc_plus_restarting_no_side_reset_keep_dead_default_recompute_controlled" !Selector.names);
  print_endline "Catching-up DefaultUpdate registrations: 13 checked"
