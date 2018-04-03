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
    Inactive

	datatype 'a chan = Ch of 'a chan_content ref * mutex_lock 

  fun channel () = Ch (ref Inactive, lock)

  fun send (Ch (contentRef, lock)) m = let
    val sendMopRef = ref (Some m)

    fun conclude () = 
      mutexRelease lock; 
      wait (sendMopRef, fn mop => mop = None);
      ()
  in 
    mutexAcquire lock;

    (case !contentRef of
      Recv q => 
        (valOf (dequeue q)) := Some m;
        if (isInactive q) then contentRef := Inactive else (); 
        () |
      Send q => 
        enqueue (q, sendMopRef);
        conclude () |
      Inactive => 
        contentRef := Send (queue [sendMopRef]);
        conclude ()
    );

  end
   
  fun recv (Ch (contentRef, lock)) =  let
    val recvMopRef = ref None

    fun conclude () =
      mutexRelease lock;
      wait (recvMopRef, fn mop => mop <> None);
      valOf (!recvMopRef)
  in 
    mutexAcquire lock;
    (case !contentRef of
      Send q => 
        let
          val sendMopRef = valOf (dequeue q)
          val m = valOf (!sendMopRef)
        in
          if (isInactive q) then contentRef := Inactive else (); 
          sendMopRef := None;
          m 
        end |
      Recv q => 
        enqueue (q, recvMopRef);  
        conclude () |
      Inactive => 
        contentRef := Recv (queue [recvMopRef]);
        conclude () |
    )
  end

end



structure OneToOneChan : CHAN = struct

  datatype 'a chan_content = 
    Active of 'a option ref | 
    Inactive  

	datatype 'a chan = Ch of 'a chan_content ref

  fun channel () = Ch (ref Intactive)

  fun send (Ch contentRef) m = let
    val sendMopRef = ref (Some m)
  in 
    case compareAndSwap (contentRef, Inactive, Active sendMopRef) of
      Inactive => 
        wait (sendMopRef, fn mop => mop = None); () |
      Active recvMopRef => 
        recvMopRef := Some m; ()
  end


  fun recv (Ch contentRef) = let
    val recvMopRef = ref None 
  in 
    case compareAndSwap (contentRef, Inactive, Active recvMopRef) of
      Inactive => 
        wait (recvMopRef, fn mop => mop <> None); 
        valOf (!recvMopRef) |
      Active sendMopRef => 
        let
          val m = valOf (!sendMopRef) 
        in
          sendMopRef := None;
          m
        end
  end

end




















