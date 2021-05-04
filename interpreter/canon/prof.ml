(* Profiling *)

type time = Gc.stat * Unix.process_times

let now () =
  let gc = Gc.quick_stat () in
  let time = Unix.times () in
  gc, time

let start () = Gc.compact (); now ()
let finish () = now ()

let diff (gc_start, time_start) (gc_end, time_end) =
  Gc.{gc_end with
    major_collections = gc_end.major_collections - gc_start.major_collections;
    minor_collections = gc_end.minor_collections - gc_start.minor_collections;
    compactions = gc_end.compactions - gc_start.compactions;
  },
  Unix.{time_end with
    tms_utime = time_end.tms_utime -. time_start.tms_utime;
    tms_stime = time_end.tms_stime -. time_start.tms_stime;
  }

let add (gc_start, time_start) (gc_end, time_end) =
  Gc.{gc_end with
    major_collections = gc_end.major_collections + gc_start.major_collections;
    minor_collections = gc_end.minor_collections + gc_start.minor_collections;
    compactions = gc_end.compactions + gc_start.compactions;
  },
  Unix.{time_end with
    tms_utime = time_end.tms_utime +. time_start.tms_utime;
    tms_stime = time_end.tms_stime +. time_start.tms_stime;
  }

let zero = let t = now () in diff t t

let print (gc, time) =
  Printf.printf "Time: user %.2f ms, system %.2f ms; GC: major %d, minor %d, compactions %d\n"
    (time.Unix.tms_utime *. 1000.0) (time.Unix.tms_stime *. 1000.0)
    gc.Gc.major_collections gc.Gc.minor_collections gc.Gc.compactions
