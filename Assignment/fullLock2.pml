/*
	Lock system template model for Assignment 2 of 2IX20 - Software Specification.
	Set up for one lock and a configurable number of ships.

	This file contains:
	- process types for locks and ships that can be used as-is for the single lock case
	- a dummy specification of the main controller
	- initialization for the single-lock, single-ship case.
*/

// The number of locks.
#define N	3
// The number of ships.
#define M	2
// The maximum number of ships immediately at either side of a lock.
#define MAX 2

// LTL formulas to be verified
// ltl e1 holds if When a request is made to open the lower doors of lock i, eventually the lower doors of lock i are open.
//ltl e1 {[]((request_low[0]?[true] == true) -> (<>(doors_status[0].lower == open)))}
// ltl e2 holds if When a request is made to open the higer doors of lock i, eventually the higer doors of lock i are open.
//ltl e2 {[]((request_high[0]?[true] == true) -> (<>(doors_status[0].higher == open)))}
// ltl f1 holds if always eventually a request is made to open the higher doors of lock N-1 
//ltl f1 {[]<>(request_high[N-1]?[true] == true)}
// ltl f2 holds if always eventually a requst is made to open the lower doors of lock 0
//ltl f2 {[]<>(request_low[0]?[true] == true)}


// Type for direction of ship.
mtype:direction = { go_down, go_down_in_lock, go_up, go_up_in_lock, goal_reached };

// Type for water level.
mtype:level = { low_level, high_level };

// Type for lock side indication.
mtype:side = { low, high };

// Type for door and slide position.
mtype:pos = { closed, open };

// Datatypes to store the status of the doors and slides of a lock.
typedef doorpairs_t {
	mtype:pos lower;
	mtype:pos higher;
}

typedef slides_t {
	mtype:pos lower;
	mtype:pos higher;
}

// Asynchronous channels to handle ship requests.
chan request_low[N] = [M] of { bool };
chan request_high[N] = [M] of { bool };
// Synchronous channels to indicate that a ship has seen that a particular pair
// of doors has opened.
chan observed_low[N] = [0] of { bool };
chan observed_high[N] = [0] of { bool };

// Status of the water level inside a lock.
mtype:level lock_water_level[N];
// Is there a ship currently in the lock?
bool lock_is_occupied[N];

// Status of the ships.
mtype:direction ship_status[M];
// Position of the ships.
byte ship_pos[M];
// Number of ships per position.
byte nr_of_ships_at_pos[N+1];

// Status and synchronous channels for doors.
doorpairs_t doors_status[N];
slides_t slide_status[N];
chan change_doors_pos[N] = [0] of { mtype:side };
chan doors_pos_changed[N] = [0] of { bool };
chan change_slide_pos[N] = [0] of { mtype:side };
chan slide_pos_changed[N] = [0] of { bool };

// Lock process type. It reacts to requests to open its doors and slides.
proctype lock(byte lockid) {
	do
	:: change_doors_pos[lockid]?low ->
    	if
    	:: doors_status[lockid].lower == closed -> doors_status[lockid].lower = open;   
        	lock_water_level[lockid] = low_level;
    	:: doors_status[lockid].lower == open -> doors_status[lockid].lower = closed;
    	fi;
    	doors_pos_changed[lockid]!true;
	:: change_doors_pos[lockid]?high ->
    	if
    	:: doors_status[lockid].higher == closed -> doors_status[lockid].higher = open;
        	if
        	:: doors_status[lockid].lower == closed && slide_status[lockid].lower == closed ->
            	lock_water_level[lockid] = high_level;
        	:: doors_status[lockid].lower == open || slide_status[lockid].lower == open -> skip;
        	fi;
    	:: doors_status[lockid].higher == open -> doors_status[lockid].higher = closed;
    	fi;
    	doors_pos_changed[lockid]!true;
	:: change_slide_pos[lockid]?low ->
    	if
    	:: slide_status[lockid].lower == closed -> slide_status[lockid].lower = open;
        	lock_water_level[lockid] = low_level;
    	:: slide_status[lockid].lower == open -> slide_status[lockid].lower = closed;
    	fi;
    	slide_pos_changed[lockid]!true;
	:: change_slide_pos[lockid]?high ->
    	if
    	:: slide_status[lockid].higher == closed -> slide_status[lockid].higher = open;
        	if
        	:: doors_status[lockid].lower == closed && slide_status[lockid].lower == closed ->
            	lock_water_level[lockid] = high_level;
        	:: doors_status[lockid].lower == open || slide_status[lockid].lower == open -> skip;
        	fi;
    	:: slide_status[lockid].higher == open -> slide_status[lockid].higher = closed;
    	fi;
    	slide_pos_changed[lockid]!true;
	od;
}

// Ship process type. Based on its direction and position, it makes requests to open doors,
// and moves when possible.
proctype ship(byte shipid) {
	do
	:: ship_status[shipid] == go_down && ship_pos[shipid] != 0 ->
    	do
        // in here lockid is ship_pos[shipid - 1]
    	:: doors_status[ship_pos[shipid] - 1].higher == closed ->
            // This is the position of the lock
        	request_high[ship_pos[shipid] - 1]!true;
        	atomic { doors_status[ship_pos[shipid] - 1].higher == open ->
            	if
            	:: !lock_is_occupied[ship_pos[shipid] - 1] ->
                    	ship_status[shipid] = go_down_in_lock;
                    	lock_is_occupied[ship_pos[shipid] - 1] = true;
                    	nr_of_ships_at_pos[ship_pos[shipid]]--;
                    	observed_high[ship_pos[shipid] - 1]!true;
                    	break;
            	:: lock_is_occupied[ship_pos[shipid] - 1] ->
                    	observed_high[ship_pos[shipid] - 1]!true;
            	fi; }
    	:: atomic { doors_status[ship_pos[shipid] - 1].higher == open &&
        	!lock_is_occupied[ship_pos[shipid] - 1] ->
            	ship_status[shipid] = go_down_in_lock;
            	lock_is_occupied[ship_pos[shipid] - 1] = true;
            	nr_of_ships_at_pos[ship_pos[shipid]]--;
            	break; }
    	od;
	:: ship_status[shipid] == go_down_in_lock ->
    	do
    	:: doors_status[ship_pos[shipid] - 1].lower == closed ->
        	request_low[ship_pos[shipid] - 1]!true;
        	atomic { doors_status[ship_pos[shipid] - 1].lower == open ->
            	if
            	:: (nr_of_ships_at_pos[ship_pos[shipid] - 1] < MAX
                	|| ship_pos[shipid] - 1 == 0) ->
                    	ship_status[shipid] = go_down;
                    	lock_is_occupied[ship_pos[shipid] - 1] = false;
                    	ship_pos[shipid]--;
                    	nr_of_ships_at_pos[ship_pos[shipid]]++;
                        //This is without the minus sign
                    	observed_low[ship_pos[shipid]]!true;
                    	break;
            	:: (nr_of_ships_at_pos[ship_pos[shipid] - 1] == MAX
                	&& ship_pos[shipid] - 1 != 0) ->
                    	observed_low[ship_pos[shipid] - 1]!true;
            	fi; }
    	:: atomic { doors_status[ship_pos[shipid] - 1].lower == open &&
        	(nr_of_ships_at_pos[ship_pos[shipid] - 1] < MAX
        	|| ship_pos[shipid] - 1 == 0) ->
            	ship_status[shipid] = go_down;
            	lock_is_occupied[ship_pos[shipid] - 1] = false;
            	ship_pos[shipid]--;
            	nr_of_ships_at_pos[ship_pos[shipid]]++;
            	break; }
    	od;
	:: ship_status[shipid] == go_up && ship_pos[shipid] != N ->
    	do
    	:: doors_status[ship_pos[shipid]].lower == closed ->
        	request_low[ship_pos[shipid]]!true;
        	atomic { doors_status[ship_pos[shipid]].lower == open ->
            	if
            	:: !lock_is_occupied[ship_pos[shipid]] ->
                    	ship_status[shipid] = go_up_in_lock;
                    	lock_is_occupied[ship_pos[shipid]] = true;
                    	nr_of_ships_at_pos[ship_pos[shipid]]--;
                    	observed_low[ship_pos[shipid]]!true;
                    	break;
            	:: lock_is_occupied[ship_pos[shipid]] ->
                    	observed_low[ship_pos[shipid]]!true;
            	fi; }
    	:: atomic { doors_status[ship_pos[shipid]].lower == open &&
        	!lock_is_occupied[ship_pos[shipid]] ->
            	ship_status[shipid] = go_up_in_lock;
            	lock_is_occupied[ship_pos[shipid]] = true;
            	nr_of_ships_at_pos[ship_pos[shipid]]--;
            	break; }
    	od;
	:: ship_status[shipid] == go_up_in_lock ->
    	do
    	:: doors_status[ship_pos[shipid]].higher == closed ->
        	request_high[ship_pos[shipid]]!true;
        	atomic { doors_status[ship_pos[shipid]].higher == open ->
            	if
            	:: (nr_of_ships_at_pos[ship_pos[shipid]+1] < MAX
                	|| ship_pos[shipid]+1 == N) ->
                    	ship_status[shipid] = go_up;
                    	lock_is_occupied[ship_pos[shipid]] = false;
                    	ship_pos[shipid]++;
                    	nr_of_ships_at_pos[ship_pos[shipid]]++;
                        //This has to minus one
                    	observed_high[ship_pos[shipid]-1]!true;
                    	break;
            	:: (nr_of_ships_at_pos[ship_pos[shipid]+1] == MAX
                	&& ship_pos[shipid]+1 != N) ->
                    	observed_high[ship_pos[shipid]]!true;
            	fi; }
    	:: atomic { doors_status[ship_pos[shipid]].higher == open &&
        	(nr_of_ships_at_pos[ship_pos[shipid]+1] < MAX
        	|| ship_pos[shipid]+1 == N) ->
            	ship_status[shipid] = go_up;
            	lock_is_occupied[ship_pos[shipid]] = false;
            	ship_pos[shipid]++;
            	nr_of_ships_at_pos[ship_pos[shipid]]++;
            	break; }
    	od;
	:: ship_status[shipid] == go_down && ship_pos[shipid] == 0 ->
    	ship_status[shipid] = goal_reached; ship_status[shipid] = go_up;
	:: ship_status[shipid] == go_up && ship_pos[shipid] == N ->
    	ship_status[shipid] = goal_reached; ship_status[shipid] = go_down;
	od;
}

proctype lock_receive(byte index) {
    do   
    :: request_low[index]?true ->
    atomic{
        if
        :: doors_status[index].lower == closed ->  
            if
            ::doors_status[index].higher == open ->  
                change_doors_pos[index]!high; doors_pos_changed[index]?true;
            ::doors_status[index].higher == closed -> skip;
            fi; 
            if
            ::slide_status[index].higher == open ->
                change_slide_pos[index]!high; slide_pos_changed[index]?true;
            ::slide_status[index].higher == closed -> skip; 
            fi;
            if
            ::lock_water_level[index] == high_level ->
                change_slide_pos[index]!low; slide_pos_changed[index]?true;
            ::lock_water_level[index] == low_level -> skip;
            fi;
        change_doors_pos[index]!low; doors_pos_changed[index]?true;
        :: doors_status[index].lower == open -> skip;
        fi;
        observed_low[index]?true;}

    :: request_high[index]?true ->
        atomic {
        if
        :: doors_status[index].higher== closed ->  
            if
            ::doors_status[index].lower == open ->  
                change_doors_pos[index]!low; doors_pos_changed[index]?true;
            ::doors_status[index].lower == closed -> skip;
            fi; 
            if
            ::slide_status[index].lower == open ->
                change_slide_pos[index]!low; slide_pos_changed[index]?true;
            ::slide_status[index].lower == closed -> skip;
            fi;
            if
            ::lock_water_level[index] == low_level ->
                change_slide_pos[index]!high; slide_pos_changed[index]?true;
            ::lock_water_level[index] == high_level -> skip; 
            fi;
        change_doors_pos[index]!high; doors_pos_changed[index]?true;
        :: doors_status[index].higher == open -> skip;
        fi;
        observed_high[index]?true;}        
    od;    
} 

//Main control process type
proctype main_control() {
    byte index = 0;
    atomic { 
    do
    :: index < N ->
        run lock_receive(index);
        index++ 
    :: index == N -> break;
    od;}
}

proctype monitor() {
	// an example assertion.
	assert(0 <= ship_pos[0] && ship_pos[0] <= N);
	//a
	assert(!(doors_status[0].lower == open && doors_status[0].higher == open));
	//b1
	assert(!(doors_status[0].lower == open) || slide_status[0].higher == closed);
	//b2
	assert(!(doors_status[0].higher == open) || (slide_status[0].lower == closed));
	//c1
	assert(!(doors_status[0].lower == open) || (lock_water_level[0] == low));
	//c2
	assert(!(doors_status[0].higher == open) || lock_water_level[0] == high); 
}    


// Initial process that instantiates all other processes and creates
// the initial lock and ship situation.
init {
	byte proc;
	atomic {
    	//run monitor();
    	run main_control();
    	proc = 0;
    	do
    	:: proc < N ->
        	doors_status[proc].lower = closed;
        	doors_status[proc].higher = closed;
        	slide_status[proc].lower = closed;
        	slide_status[proc].higher = closed;
        	lock_water_level[proc] = high_level;
        	lock_is_occupied[proc] = false;
        	run lock(proc);
        	proc++;
    	:: proc == N -> break;
    	od;
    	// In the code below, the individual ship positions and directions
    	// are initialised. Expand this when more ships should be added.
    	proc = 0;
    	do
    	:: proc < M -> ship_status[proc] = go_up; ship_pos[proc] = 0;
        	run ship(proc); proc++;
    	:: proc == M -> break;
    	od;
    	// Do not change the code below It derives the number of ships per
    	// position from the positions of the individual ships.
    	proc = 0;
    	do
    	:: proc < M -> nr_of_ships_at_pos[ship_pos[proc]]++; proc++;
    	:: else -> break;
    	od;
	}
}
