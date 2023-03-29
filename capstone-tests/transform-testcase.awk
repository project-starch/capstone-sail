BEGIN {
    started = 0;
}

{
    if(started == 1)
        print $0;
}

/_start:/ {
    started = 1;
}
