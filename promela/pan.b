	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* PROC :init: */

	case 3: // STATE 2
		;
		((P1 *)_this)->lastpid = trpt->bup.oval;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 4: // STATE 4
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Hello */
;
		;
		
	case 6: // STATE 2
		;
		p_restor(II);
		;
		;
		goto R999;
	}

