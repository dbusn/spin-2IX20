proctype Alpha(int x) {
    int y=1;
    skip;
    run Omega();
    x=2;
    x>2 && y==1;
    skip;
}

proctype Omega() {
    skip;
}

init {
    run Alpha(5);
}
