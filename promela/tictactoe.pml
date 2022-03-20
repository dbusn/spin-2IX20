/* Player, used to represent tokens on grid, turns and winner */
mtype:player = {cX, cO, cNone};
mtype:message = {aBeginTurn, aEndTurn};

mtype grid[9] = {
	cNone, cNone, cNone,
	cNone, cNone, cNone,
	cNone, cNone, cNone
};

chan comPlayerX = [0] of { mtype:message };
chan comPlayerO = [0] of { mtype:message };

#define WINS(grid, p) \
	(	(grid[0] == p && grid[1] == p && grid[2] == p) \
	||	(grid[3] == p && grid[4] == p && grid[5] == p) \
	||	(grid[6] == p && grid[7] == p && grid[8] == p) \
	||	(grid[0] == p && grid[3] == p && grid[6] == p) \
	||	(grid[1] == p && grid[4] == p && grid[7] == p) \
	||	(grid[2] == p && grid[5] == p && grid[8] == p) \
	||	(grid[0] == p && grid[4] == p && grid[8] == p) \
	||	(grid[2] == p && grid[4] == p && grid[6] == p) )

#define DRAWS(grid) \
	(	(grid[0] != cNone && grid[1] != cNone && grid[2] != cNone \
	&&	grid[3] != cNone && grid[4] != cNone && grid[5] != cNone \
	&&	grid[6] != cNone && grid[7] != cNone && grid[8] != cNone) \
	&& !WINS(grid, cX)
	&& !WINS(grid, cO) )

active proctype PlayerX()
{
	do
	::
		comPlayerX?aBeginTurn;
		if
		:: (grid[0] == cNone) -> grid[0] = cX;
		:: (grid[1] == cNone) -> grid[1] = cX;
		:: (grid[2] == cNone) -> grid[2] = cX;
		:: (grid[3] == cNone) -> grid[3] = cX;
		:: (grid[4] == cNone) -> grid[4] = cX;
		:: (grid[5] == cNone) -> grid[5] = cX;
		:: (grid[6] == cNone) -> grid[6] = cX;
		:: (grid[7] == cNone) -> grid[7] = cX;
		:: (grid[8] == cNone) -> grid[8] = cX;
		fi
		comPlayerX!aEndTurn;
	od
}

active proctype PlayerO()
{
	do
	::
		comPlayerO?aBeginTurn;
		if
		:: (grid[0] == cNone) -> grid[0] = cO;
		:: (grid[1] == cNone) -> grid[1] = cO;
		:: (grid[2] == cNone) -> grid[2] = cO;
		:: (grid[3] == cNone) -> grid[3] = cO;
		:: (grid[4] == cNone) -> grid[4] = cO;
		:: (grid[5] == cNone) -> grid[5] = cO;
		:: (grid[6] == cNone) -> grid[6] = cO;
		:: (grid[7] == cNone) -> grid[7] = cO;
		:: (grid[8] == cNone) -> grid[8] = cO;
		fi
		comPlayerO!aEndTurn;
	od;
}

active proctype Game()
{
	mtype turn = cX;
	mtype won = cNone;

	do
	:: (WINS(grid, cX)) ->
		turn = cNone;
		won = cX;
		printf("Player X wins")
		break;

	:: (WINS(grid, cO)) ->
		turn = cNone;
		won = cO;
		printf("Player Y wins")
		break;

	:: (DRAWS(grid)) ->
		turn = cNone;
		won = cNone;
		printf("It's a draw")
		break;

	:: else ->
		if
		:: (turn == cX) ->
			comPlayerX!aBeginTurn;
			comPlayerX?aEndTurn;
			turn = cO;

		:: (turn == cO) ->
			comPlayerO!aBeginTurn;
			comPlayerO?aEndTurn;
			turn = cX;
		fi
	od
}
