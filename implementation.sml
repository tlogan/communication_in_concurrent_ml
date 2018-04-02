signature CHAN = sig
  type 'a chan 
  val channel: unit -> 'a chan
  val send: 'a chan * 'a -> unit
  val recv: 'a chan -> 'a
end


structure CourseGrainChan : CHAN = struct

	datatype 'a chan = Ch of 'a chan_content ref  
  and 'a chan_content = 
    Send of 'a message_queue | 
    Recv of 'a message_queue | 
    Empty
  withtype message_queue = 'a option ref queue

  fun channel () = Empty

  fun send (Ch contentRef) m = let
    val sendMopRef = ref (Some m)
  in 
    mutexAcquire contentRef;

    (case !contentRef of
      Recv q => 
        (dequeue q) := Some m;
        if (isEmpty q) then contentRef := Empty else (); 
        sendMopRef := None |
      Send q => enqueue (q, sendMopRef) |
      Empty => contentRef := Send (queue sendMopRef) );

    mutexRelease contentRef;

    wait (sendMopRef, fn mop => mop = None);

    ()
  end
   
  fun recv (Ch contentRef) =  let
    val recvMopRef = ref None
  in 
    mutexAcquire contentRef;

    (case !contentRef of
      Send q => 
        let
          val sendMopRef = dequeue q
          val mop = !sendMopRef
        in
          if (isEmpty q) then contentRef := Empty else (); 
          sendMopRef := None;
          recvMopRef := mop
        end |
      Recv q => enqueue (q, recvMopRef) |
      Empty => contentRef := Recv (queue recvMopRef)
    );

    mutexRelease contentRef;

    wait (recvMopRef, fn mop => mop <> None);

    valOf (!recvMopRef)
  end

end


