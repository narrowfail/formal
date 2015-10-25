/*
    Simple proportional control.
    Obtains input data for the reference and the feedback, and
    generates a proportional control value using the equation:

    u = Kp(r – b) + P

    b is obtained from c * Kb, where c is the output of the
    controlled device or system (the plant), and Kb is a gain
    applied to scale it into the same range as the r (reference)
    input.

    The gain parameters Kp and Kb should be set to something
    meaningful for a specific application. The P parameter is
    the bias to be applied to the output.

    Source:
    Real World Instrumentation with Python
    Automated Data Acquisition and Control Systems
    By John M. Hughes
    Publisher: O'Reilly Media
    Page: 341
*/

class ProportionalControl{
    var kp: real;
    var kb: real;
    var p: real;

    // Anonymous constructor
    constructor ()
    modifies this
    {
        kp := 1.0;
        kb := 1.0;
        p := 0.0;
    }

    // TODO Test this constructor!
    constructor ProportionalControl(newKp: real, newKb: real, newP: real)
    modifies this;
    {
        kp := newKp;
        kb := newKb;
        p := newP;
    }

    method PControl(rinput: real, cinput: real) returns (output: real)
    {
        var eval := rinput - (cinput * kb);
        return (kp * eval) + p;
    }
}
