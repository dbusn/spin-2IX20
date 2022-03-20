#define	N	2 /* dimension of channels */
#define	MAX	2 /* Send integers modulo MAX */

mtype = { MSG, ACK, ERROR };

chan fromS = [N] of { mtype, byte, bit };	/* From S to unreliable channel */
chan toR = [N] of { mtype, byte, bit };   	/* From unreliable channel to R */
chan fromR = [N] of { mtype, bit };       	/* From R to unreliable channel */
chan toS = [N] of { mtype, bit };		/* From unreliable channel to s */

byte last_m = MAX-1;		/* data of last error-free message, for verification */

//ltl msg_zero { <>(last_m == 0) };
ltl msg_one { <>(last_m == 1) };
//ltl infinitelyoftenzero { []<>(last_m == 1) };
	
proctype Sender(chan in,out) {
  bit sendbit; 	/* alternation bit transmitted */
  bit recvbit;	/* alternation bit received */
  byte m;      	/* message data */

  out ! MSG(m,sendbit) ->	/* Send current message */
  do
  :: in ? ACK(recvbit);		/* Await response */
     if
     :: recvbit == sendbit ->	/* Successful transmission */
        sendbit = 1-sendbit;	/* Toggle bit */
        m = (m+1)%MAX		/* Get new message */
     :: else ->
        skip		       	/* Transmission error, don't get new msg */
     fi;
     out ! MSG(m,sendbit) ->	/* Send message (either old or new) */
  :: in ? ERROR(recvbit) ->	/* Receive error */
     out ! MSG(m,sendbit)	/* Send again */
  od;
}

proctype Receiver(chan in,out) {
  byte m;			/* message data received */
  bit recvbit;			/* alternation bit received */
  bit last_recvbit = 1;		/* receive bit of last error-free message */

  do
  :: in ? MSG(m, recvbit) -> 	       	/* Message received successfully */
     out ! ACK(recvbit);			/* Send acknowledgement with received bit */
     if
     :: (recvbit == last_recvbit) ->	/* bit is not alternating, old message */
        skip				/* don't accept message */
     :: (recvbit != last_recvbit) -> 	/* bit is alternating; accept message */
        printf("ACCEPT %d\n", m);
        assert(m == (last_m+1)%MAX);	/* check that we accept only correct messages */
        last_recvbit = recvbit;		/* store alternating bit */
        last_m = m			/* store m */
     fi
  :: in ? ERROR(m, recvbit) ->		/* Receive error */
     out ! ACK(last_recvbit)		/* Send ack with old bit */
  od;
}

proctype unreliable_channel_bit(chan in, out) {
  bit b;  /* Bit received from input */

  do
  :: in ? ACK(b) ->  	/* Receive ack along input channel */
     if
     ::out ! ACK(b); 	/* Correct transmission */
     ::out ! ERROR(0);	/* Corrupted */
     fi
  od
}

proctype unreliable_channel_data(chan in, out) {
  byte d;		/* Data received from input */
  bit b;		/* Bit received from input */

  do
  :: in ? MSG(d,b) -> 	/* Receive transmission along input channel */
     if
     ::out ! MSG(d,b); 	/* Correct transmission */
     ::out ! ERROR(0,0);	/* Corrupted */
     fi
  od
}

init {
  run Sender(toS, fromS);
  run Receiver(toR, fromR);
  run unreliable_channel_bit(fromR, toS);
  run unreliable_channel_data(fromS, toR);
}
