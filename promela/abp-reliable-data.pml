#define	N	2   /* dimension of channels */
#define	MAX	8 /* MAX value to send */

mtype = { MSG, ACK };
chan toR = [N] of { mtype, byte, bit }; /* Channel from S to R */
chan toS = [N] of { mtype, bit };       /* Channel from R to S */

proctype Sender(chan in,out) {
  bit sendbit; 	/* alternation bit transmitted */
  bit recvbit;	/* alternation bit received */
  byte m;	      /* message data */

  do
  :: out ! MSG(m,sendbit) ->	/* Send current message */
     in ? ACK(recvbit);		    /* Await response */
     if
     :: recvbit == sendbit ->	/* Successful transmission */
        sendbit = 1-sendbit;	/* Toggle bit */
        m = (m+1)%MAX		      /* Get new message */
     :: else -> skip;		      /* Transmission error, don't get new msg */
     fi;
  od;
}

proctype Receiver(chan in,out) {
  byte m; 	    /* message data received */
  bit recvbit;	/* alternation bit received */
  do
  :: in ? MSG(m, recvbit) -> 	/* Message received successfully */
     out ! ACK(recvbit);		  /* Send acknowledgement with received bit */
  od;
}

init {
  run Sender(toS, toR);
  run Receiver(toR, toS);
}
