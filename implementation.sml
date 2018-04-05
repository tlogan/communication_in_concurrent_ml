signature CHAN = sig
  type 'a chan 
  val channel: unit -> 'a chan
  val send: 'a chan * 'a -> unit
  val recv: 'a chan -> 'a
end


structure ManyToManyChan : CHAN = struct

  type message_queue = 'a option ref queue

  datatype 'a chan_content = 
    Send of (condition * 'a) queue | 
    Recv of (condition * 'a option ref) queue | 
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
        end |
      Send q => 
        let
          val sendCond = condition () 
        in
          enqueue (q, (sendCond, m));
          release lock;
          wait sendCond;
          () 
        end |
      Inactive => 
        let
          val sendCond = condition () 
        in
          contentRef := Send (queue [(sendCond, m)]);
          release lock;
          wait sendCond;
          ()
        end)
   
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
          val recvCond = condition ()
          val mopRef = ref None
        in
          enqueue (q, (recvCond, mopRef));
          release lock;
          wait recvCond;
          valOf (!mopRef) | 
        end
      Inactive =>
        let
          val recvCond = condition ()
          val mopRef = ref None
        in
          contentRef := Recv (queue [(recvCond, mopRef)]);
          release lock;
          wait recvCond;
          valOf (!mopRef)
        end)

end



structure FanOutChan : CHAN = struct

  datatype 'a chan_content =
    Send of condition * 'a |
    Recv of (condition * 'a option ref) queue  |
    Inactive
  
	datatype 'a chan = Ch of 'a chan_content ref * mutex_lock

  fun channel () = Ch (ref Inactive, mutexLock ())

  fun send (Ch (contentRef, lock)) m = let
    val sendCond = condition () 
  in
    case compareAndSwap (contentRef, Inactive, Send (sendCond, m)) of
      Inactive =>
        (* contentRef already set *)
        wait sendCond;
        () |
      Recv q => 
        (* the current thread is the only one that upates from this state *)
        acquire lock;
        (let
          val (recvCond, mopRef) = dequeue q
        in
          mopRef := Some m; 
          if (isEmpty q) then contentRef := Inactive else (); 
          release lock;
          signal (recvCond);
          () 
        end) |
      Send _ => raise NeverHappens
    end

  fun recv (Ch (contentRef, lock)) =
    acquire lock;
    (case !contentRef of
      Inactive =>
        let
          val recvCond = condition ()
          val mopRef = ref None
        in
          contentRef := Recv (queue [(recvCond, mopRef)]);
          release lock;
          wait recvCond;
          valOf (!mopRef) 
        end |
      Recv q => 
        let
          val recvCond = condition () 
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
          val sendCond = condition () 
        in
          enqueue (q, (sendCond, m));
          release lock;
          wait sendCond;
          () 
        end |
      Inactive => 
        let
          val sendCond = condition () 
        in
          contentRef := Send (queue [(sendCond, m)])
          release lock;
          wait sendCond;
          ()
        end 


  fun recv (Ch (contentRef, lock)) = let
    val recvCond = condition () 
    val mopRef = ref None
  in
    case compareAndSwap (contentRef, Inactive, Recv (recvCond, mopRef)) of
      Inactive =>   
        (* contentRef already set *)
        wait recvCond;
        valOf (!mopRef) |
      Send q => 
        (* the current thread is the only one that updates the state from this state *)
        acquire lock;
        (let
          val (sendCond, m) = dequeue q
        in
          if (isEmpty q) then contentRef := Inactive else (); 
          release lock;
          signal sendCond;
          m 
        end) |
      Recv _ => raise NeverHappens
  
  end

end


structure OneToOneChan : CHAN = struct

  datatype 'a chan_content =
    Send of condition * 'a |
    Recv of condition * 'a option ref |
    Inactive  

	datatype 'a chan = Ch of 'a chan_content ref

  fun channel () = Ch (ref Inactive)

  fun send (Ch contentRef) m = let
    val sendCond = condition () 
  in
    case compareAndSwap (contentRef, Inactive, Send (sendCond, m)) of
      Intactive => 
        (* contentRef already set to Send *)
        wait sendCond; 
        () |
      Recv (recvCond, mopRef) =>
        (* the current thread is the only one that accesses contentRef for this state*)
        mopRef := Some m;
        contentRef := Inactive;
        signal recvCond;
        () |
      Send _ => raise NeverHappens
  end


  fun recv (Ch contentRef) = let
    val recvCond = condition ();
    val mopRef = ref None;
  in
    case compareAndSwap (contentRef, Inactive, Recv (recvCond, mopRef)) of
      Inactive => 
        (* contentRef already set to Recv*)
        wait recvCond; 
        valOf (!mopRef) |
      Send (sendCond, m) =>
        (* the current thread is the only one that accesses contentRef for this state*)
        contentRef := Inactive;
        signal sendCond;
        m |
      Recv _ => raise NeverHappens
  end
      

end

structure OneShotToManyChan : CHAN = struct

  datatype 'a chan_content =
    Send of condition * 'a |
    Recv of condition * 'a option ref |
    Inactive  

  datatype 'a chan = Ch of 'a chan_content ref * mutex_lock

  fun channel () = Ch (ref Inactive, lock ())

  fun send (Ch (contentRef, lock)) m = let
    val sendCond = condition ()
  in
    case (contentRef, Inactive, Send (sendCond, m)) of
      Inactive =>
        (* contentRef already set to Send*)
        wait sendCond; 
        () |
      Recv (recvCond, mopRef) =>
        mopRef := Some m; 
        signal recvCond;
        () |
      Send _ => raise NeverHappens
  end


  fun recv (Ch (contentRef, lock)) = let
    val recvCond = condition ()
    val mopRef = ref None
  in
    case (contentRef, Inactive, Recv (recvCond, mopRef)) of
      Inactive =>
        (* contentRef already set to Recv*)
        wait recvCond;
        valOf (!mopRef) |
      Send (sendCond, m) =>
        acquire lock;
        signal sendCond;
        (* never relases lock; blocks others forever *)
        m |
      Recv _ =>
        acquire lock;
        (* never able to acquire lock; blocked forever *)
        raise NeverHappens

end



structure OneShotToOneChan : CHAN = struct

	datatype 'a chan = Ch of condition * condition * 'a option ref

  fun channel () = Ch (condition (), condition (), ref None)

  fun send (Ch (sendCond, recvCond, mopRef)) m =
    mopRef := Some m;
    signal recvCond;  
    wait sendCond;
    ()


  fun recv (Ch (sendCond, recvCond, mopRef)) =
    wait recvCond;
    signal sendCond;
    valOf (!mopRef)

end























