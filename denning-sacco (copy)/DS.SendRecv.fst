module DS.SendRecv


(* Needs access to internal clock implementation *)
friend DS.Clock


let send #i c_in sender receiver message =
  let c_out = clock_add c_in 1 in
  let si = send #S.ds_preds #i sender receiver message in
  (|si,c_out|)

let receive_i i c_in receiver =
  let c_out = clock_add c_in 1 in
  let (|now,sender,t|) = receive_i #S.ds_preds i receiver in
  (|now,c_out,sender,t|)
