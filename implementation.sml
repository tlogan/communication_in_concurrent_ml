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

  fun channel () = Ch (ref Inactive, mutexLock ())

  fun send (Ch (contentRef, lock)) m = 
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
        let
          val sendCond = condition lock 
        in
          enqueue (q, (sendCond, m));
          release lock;
          wait sendCond;
          () 
        end |
      Inactive => 
        let
          val sendCond = condition lock 
        in
          contentRef := Send (queue [(sendCond, m)]);
          release lock;
          wait sendCond;
          ()
        end
    )
   
  fun recv (Ch (contentRef, lock)) =  
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
        let
          val recvCond = condition lock
          val mopRef = ref None
        in
          enqueue (q, (recvCond, mopRef));
          release lock;
          wait recvCond;
          valOf (!mopRef) | 
        end
      Inactive =>
        let
          val recvCond = condition lock
          val mopRef = ref None
        in
          contentRef := Recv (queue [(recvCond, mopRef)]);
          release lock;
          wait recvCond;
          valOf (!mopRef)
        end
    )

end



structure FanOutChan : CHAN = struct

  datatype 'a chan_content =
    Send of condition * 'a |
    Recv of condition queue * 'a option ref |
    Inactive
  
	datatype 'a chan = Ch of 'a chan_content ref * mutex_lock

  fun channel () = Ch (ref Inactive, mutexLock ())

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

          acquire lock;
          if (isEmpty q) then contentRef := Inactive else (); 
          release lock;

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
          val mopRef = ref None
        in
          enqueue (q, (recvCond, mopRef));
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

  fun channel () = Ch (ref Inactive, mutexLock ())

  fun send (Ch (contentRef, lock)) m = 
    acquire lock;
    case !contentRef of
      Recv (recvCond, mopRef) => 
        mopRef := Some m;
        contentRef := Inactive;
        release lock;
        signal recvCond;
        () |
      Send q =>
        let
          val sendCond = condition lock 
        in
          enqueue (q, (sendCond, m));
          release lock;
          wait sendCond;
          () 
        end |
      Inactive => 
        let
          val sendCond = condition lock 
        in
          contentRef := Send (queue [(sendCond, m)])
          release lock;
          wait sendCond;
          ()
        end 
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
          acquire lock;
          if (isEmpty q) then contentRef := Inactive else (); 
          release lock;
          signal sendCond;
          m 
        end
      Recv _ => raise NeverHappens
  
  end

end


structure OneToOneChan : CHAN = struct

  datatype 'a chan_content =
    Send of condition * 'a |
    Recv of condition * 'a option ref |
    Inactive  

	datatype 'a chan = Ch of 'a chan_content ref * mutex_lock

  fun channel () = Ch (ref Inactive, mutexLock ())

  fun send (Ch (contentRef, lock)) m = let
    val sendCond = condition lock 
  in
    case compareAndSwap (contentRef, Inactive, Send (sendCond, m)) of
      Intactive => 
        (* contentRef already set to Send *)
        wait sendCond; 
        () |
      Recv (recvCond, mopRef) =>
        mopRef := Some m;
        contentRef := Inactive;
        signal recvCond;
        () |
      Send _ => raise NeverHappens
  end


  fun recv (Ch (contentRef, lock)) = let
    val recvCond = condition lock;
    val mopRef = ref None;
  in
    case compareAndSwap (contentRef, Inactive, Recv (recvCond, mopRef)) of
      Inactive => 
        (* contentRef already set to Recv*)
        wait recvCond; 
        valOf (!mopRef) |
      Send (sendCond, m) =>
        contentRef := Inactive;
        signal sendCond;
        m |
      Recv _ => raise NeverHappens
  end
      

end



structure OneShotChan : CHAN = struct

	datatype 'a chan = Ch of condition * 'a option ref

  fun channel () = let
    val lock = mutexLock ()
    val cond = condition lock
  in
    Ch (cond, ref None)
  end

  fun send (Ch (cond, mopRef)) m =
    case !mopRef of
      None => 
        mopRef := Some m;
        signal cond; 
        wait cond; 
        () |
      Some _ => raise NeverHappens


  fun recv (Ch (cond, mopRef)) =
    case !mopRef of
      None => 
        wait cond; 
        signal cond; 
        valOf (!mopRef) |
      Some m =>
        signal cond; 
        m

end























