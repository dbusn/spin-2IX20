chan ch = [0] of {bit, byte};

active proctype P {
  ch!1,3+7;
}

active proctype Q {
  byte x;
  ch?1,x;
}
