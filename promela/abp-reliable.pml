#define	N	2 /* dimension of channels */

mtype = { MSG, ACK };
chan toR = [N] of { mtype, bit };   /* Channel from S to R */
chan toS = [N] of { mtype, bit };   /* Channel from R to S */

proctype Sender(chan in,out) {
  bit sendbit; 	/* alternation bit transmitted */
  bit recvbit;	/* alternation bit received */

  do
  :: out ! MSG(sendbit) ->     /* Send current message */
     in ? ACK(recvbit);        /* Await response */
     if
     :: recvbit == sendbit -> /* Successful transmission */
        sendbit = 1-sendbit;  /* Toggle bit */
     :: else -> skip;         /* Transmission error, don't get new msg */
     fi;
  od;
}

proctype Receiver(chan in,out) {
  bit recvbit;  /* alternation bit received */
  do
  :: in ? MSG(recvbit) -> /* Message received successfully */
     out ! ACK(recvbit);  /* Send acknowledgement with received bit */
  od;
}

init {
  run Sender(toS, toR);
  run Receiver(toR, toS);
}
