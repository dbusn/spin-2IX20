#define rand	pan_rand
#define pthread_equal(a,b)	((a)==(b))
#if defined(HAS_CODE) && defined(VERBOSE)
	#ifdef BFS_PAR
		bfs_printf("Pr: %d Tr: %d\n", II, t->forw);
	#else
		cpu_printf("Pr: %d Tr: %d\n", II, t->forw);
	#endif
#endif
	switch (t->forw) {
	default: Uerror("bad forward move");
	case 0:	/* if without executable clauses */
		continue;
	case 1: /* generic 'goto' or 'skip' */
		IfNotBlocked
		_m = 3; goto P999;
	case 2: /* generic 'else' */
		IfNotBlocked
		if (trpt->o_pm&1) continue;
		_m = 3; goto P999;

		 /* PROC :init: */
	case 3: // STATE 1 - hello.pml:7 - [printf('init, my pid is: %d\\n',_pid)] (0:4:1 - 1)
		IfNotBlocked
		reached[1][1] = 1;
		Printf("init, my pid is: %d\n", ((int)((P1 *)_this)->_pid));
		/* merge: lastpid = run Hello()(4, 2, 4) */
		reached[1][2] = 1;
		(trpt+1)->bup.oval = ((P1 *)_this)->lastpid;
		((P1 *)_this)->lastpid = addproc(II, 1, 0);
#ifdef VAR_RANGES
		logval(":init::lastpid", ((P1 *)_this)->lastpid);
#endif
		;
		/* merge: printf('last pid was: %d\\n',lastpid)(4, 3, 4) */
		reached[1][3] = 1;
		Printf("last pid was: %d\n", ((P1 *)_this)->lastpid);
		_m = 3; goto P999; /* 2 */
	case 4: // STATE 4 - hello.pml:10 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[1][4] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Hello */
	case 5: // STATE 1 - hello.pml:2 - [printf('Hello, my pid is: %d\\n',_pid)] (0:0:0 - 1)
		IfNotBlocked
		reached[0][1] = 1;
		Printf("Hello, my pid is: %d\n", ((int)((P0 *)_this)->_pid));
		_m = 3; goto P999; /* 0 */
	case 6: // STATE 2 - hello.pml:3 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[0][2] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */
	case  _T5:	/* np_ */
		if (!((!(trpt->o_pm&4) && !(trpt->tau&128))))
			continue;
		/* else fall through */
	case  _T2:	/* true */
		_m = 3; goto P999;
#undef rand
	}

