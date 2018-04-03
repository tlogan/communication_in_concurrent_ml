signature CHAN = sig
  type 'a chan 
  val channel: unit -> 'a chan
  val send: 'a chan * 'a -> unit
  val recv: 'a chan -> 'a
end


structure ManyToManyChan : CHAN = struct

  type message_queue = 'a option ref queue

  datatype 'a chan_content = 
    Send of 'a message_queue | 
    Recv of 'a message_queue | 
    Empty

	datatype 'a chan = Ch of 'a chan_content ref * mutex_lock 

  fun channel () = Ch (ref Empty, lock)

  fun send (Ch (contentRef, lock)) m = let
    val sendMopRef = ref (Some m)
  in 
    mutexAcquire lock;

    (case !contentRef of
      Recv q => 
        (valOf (dequeue q)) := Some m;
        if (isEmpty q) then contentRef := Empty else (); 
        sendMopRef := None |
      Send q => enqueue (q, sendMopRef) |
      Empty => contentRef := Send (queue [sendMopRef]));

    mutexRelease lock;

    wait (sendMopRef, fn mop => mop = None);

    ()
  end
   
  fun recv (Ch (contentRef, lock)) =  let
    val recvMopRef = ref None
  in 
    mutexAcquire lock;

    (case !contentRef of
      Send q => 
        let
          val sendMopRef = valOf (dequeue q)
          val mop = !sendMopRef
        in
          if (isEmpty q) then contentRef := Empty else (); 
          sendMopRef := None;
          recvMopRef := mop
        end |
      Recv q => enqueue (q, recvMopRef) |
      Empty => contentRef := Recv (queue [recvMopRef])
    );

    mutexRelease lock;

    wait (recvMopRef, fn mop => mop <> None);

    valOf (!recvMopRef)
  end

end

























