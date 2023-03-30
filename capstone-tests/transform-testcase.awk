BEGIN {
    started = 0;
    print "__start__:";
}

{
    if(started == 1) {
        gsub(/_start/, "__start__");
        # so they still point to the beginning
        print $0;
    }
}

/_start:/ {
    started = 1;
}
