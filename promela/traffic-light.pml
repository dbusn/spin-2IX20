mtype = {RED, YELLOW, GREEN};

active proctype TrafficLight() {
  mtype state = GREEN;
  do
  :: (state == GREEN)   -> state = YELLOW;
  :: (state == YELLOW)  -> state = RED;
  :: (state == RED)     -> state = GREEN;
  od;
}
