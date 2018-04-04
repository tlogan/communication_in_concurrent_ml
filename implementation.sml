signature CHAN = sig
  type 'a chan 
  val channel: unit -> 'a chan
  val send: 'a chan * 'a -> unit
  val recv: 'a chan -> 'a
end


structure ManyToManyChan : CHAN = struct

  type message_queue = 'a option ref queue

  datatype 'a chan_content = 
    Send of (cond * 'a) queue | 
    Recv of (cond  * 'a option ref) queue | 
    Inactive

	datatype 'a chan = Ch of 'a chan_content ref * mutex_lock 

  fun channel () = Ch (ref Inactive, lock)

  fun send (Ch (contentRef, lock)) m = let
    val sendCond = condition lock 
  in
    acquire lock;
    (case !contentRef of
      Recv q => 
        let
          val (recvCond, mopRef) = dequeue q
        in
          mopRef := Some m;
          if (isEmpty q) then contentRef := Inactive else (); 
          release lock;
          signal recvCond; 
          () 
        end
        () |
      Send q => 
        enqueue (q, (sendCond, m));
        release lock;
        wait sendCond;
        () |
      Inactive => 
        contentRef := Send (queue [(sendCond, m)]);
        release lock;
        wait sendCond;
        ()
    )
  end
   
  fun recv (Ch (contentRef, lock)) =  let
    val recvCond = condition lock
    val mopRef = ref None
  in
    acquire lock;
    (case !contentRef of 
      Send q =>
        let
          val (sendCond, m) = dequeue q
        in
          if (isEmpty q) then contentRef := Inactive else (); 
          release lock;
          signal sendCond; 
          m
        end |
      Recv q =>
        enqueue (q, (recvCond, mopRef));
        release lock;
        wait recvCond;
        valOf (!mopRef) | 
      Inactive =>
        contentRef := Recv (queue [(recvCond, mopRef)]);
        release lock;
        wait recvCond;
        valOf (!mopRef)
    )
  end

end



structure FanOutChan : CHAN = struct

  datatype 'a chan_content =
    Send of condition * 'a |
    Recv of condition queue * 'a option ref |
    Inactive
  
	datatype 'a chan = Ch of 'a chan_content ref * mutex_lock

  fun channel () = Ch (ref Inactive, lock)

  fun send (Ch (contentRef, lock)) m = let
    val sendCond = condition lock 
  in
    case compareAndSwap (contentRef, Inactive, Send (sendCond, m)) of
      Inactive =>
        (* contentRef already set *)
        wait sendCond;
        () |

      Recv (q, mopRef) => 
        let
          val recvCond = dequeue q
        in
          mopRef := Some m; 
          if (isEmpty q) then contentRef := Inactive else (); 
          signal (recvCond);
          () 
        end |

      Send _ => raise NeverHappens
  end

  fun recv (Ch (contentRef, lock)) =
    acquire lock;
    (case !contentRef of
      Inactive =>
        let
          val recvCond = condition lock 
          val mopRef = ref None
        in
          contentRef := Recv (queue [recvCond], mopRef);
          release lock;
          wait recvCond;
          valOf (!mopRef) 
        end |
      Recv (q, mopRef) => 
        let
          val recvCond = condition lock 
        in
          enqueue (q, recvCond);
          release lock;
          wait recvCond;
          valOf (!mopRef) 
        end |
      Send (sendCond, m) =>
        contentRef := Inactive;
        release lock;
        signal sendCond;
        m
    ) 
end



structure FanInChan : CHAN = struct

  datatype 'a chan_content =
    Send of (condition * 'a) queue |
    Recv of condition * 'a option ref |
    Inactive
  
	datatype 'a chan = Ch of 'a chan_content ref * mutex_lock

  fun channel () = Ch (ref Inactive, lock)

  fun send (Ch (contentRef, lock)) m = let
    val sendCond = condition lock 
  in
    acquire lock;
    case !contentRef of
      Recv (cond, mopRef) => 
        mopRef := Some m;
        contentRef := Inactive;
        release lock;
        signal cond;
        () |
      Send q =>
        enqueue (q, (sendCond, m));
        release lock;
        wait sendCond;
        () |
      Inactive => 
        contentRef := Send (queue [(sendCond, m)])
        release lock;
        wait sendCond;
        ()
  end


  fun recv (Ch (contentRef, lock)) = let
    val recvCond = condition lock 
    val mopRef = ref None
  in
    case compareAndSwap (contentRef, Inactive, Recv (recvCond, mopRef)) of
      Inactive =>   
        (* contentRef already set *)
        wait recvCond;
        valOf (!mopRef) |
      Send q => 
        let
          val (sendCond, m) = dequeue q
        in
          if (isEmpty q) then contentRef := Inactive else (); 
          signal sendCond;
          m 
        end
      Recv _ => raise NeverHappens
  
  end

end



structure OneShotChan : CHAN = struct

  datatype 'a chan_content =
    Send of condition * 'a |
    Recv of condition * 'a option ref |
    Inactive  

	datatype 'a chan = Ch of 'a chan_content ref * mutex_lock

  fun channel () = Ch (ref Inactive)

  fun send (Ch (contentRef, lock)) m = let
    val sendCond = condition lock 
  in
    case !contentRef of
      Inactive => 
        contentRef := Send (sendCond, m);
        wait sendCond; 
        () |
      Recv (recvCond, mopRef) =>
        mopRef := Some m;
        signal recvCond;
        () |
      Send _ => raise NeverHappens
  end


  fun recv (Ch (contentRef, lock)) = let
    val recvCond = condition lock;
    val mopRef = ref None;
  in
    case !contentRef of
      Inactive => 
        contentRef := Recv (recvCond, mopRef)
        wait recvCond; 
        valOf (!mopRef) |
      Send (sendCond, m) =>
        signal sendCond;
        m |
      Recv _ => raise NeverHappens
  end
      

end














