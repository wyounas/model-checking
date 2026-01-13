/*
 * santa_bug_deliver_and_consult_simultaneously.pml
 *
 * Buggy Santa Claus model: delivery and consultation at the same time
 * -------------------------------------------------------------------
 *
 * This model intentionally violates a core constraint of the Santa Claus
 * concurrency puzzle: Santa must perform one indivisible action at a time.
 * In a correct solution, Santa cannot be delivering toys and consulting with
 * elves simultaneously.
 *
 * An explanation of this model and how it exhibits the bug is part of
 * the blog post:
 * http://wyounas.github.io/puzzles/concurrency/2025/12/23/how-to-help-santa-claus-concurrently/
 *
 * How to run this model and see the failure:
 *
 *   1) Generate the verifier:
 *        spin -a santa_bug_deliver_and_consult_simultaneously.pml
 *
 *   2) Compile the verifier:
 *        gcc -O2 -o pan pan.c
 *
 *   3) Run the verification:
 *        ./pan
 *
 *      SPIN will report an assertion violation (assert fails).
 *
 *   4) Replay the counterexample trace:
 *        spin -p -t santa_bug_deliver_and_consult_simultaneously.pml
 *
 *      In the trace, you can see an interleaving where both Santa processes
 *      overlap such that delivering and consulting are true at the same time,
 *      which triggers:
 *
 *          assert !(consulting && delivering);
 *
 */

#define NUM_REINDEER 9
#define NUM_ELVES 3


chan r_arrive = [0] of { bit };
chan e_arrive = [0] of { bit };

byte r_count = 0;
byte e_count = 0;
bool delivering = false;
bool consulting = false;



/* Track if reindeer are waiting */


active [NUM_REINDEER] proctype Reindeer()
{
    do
    ::
        r_arrive ! 1;
       
    od
}

active [NUM_ELVES] proctype Elves()
{
    do
    ::
        e_arrive ! 1;
 
    od
}

active proctype SantaConsulting()
{

 byte e = 0;
    byte j;
    end:
    do
    
    :: (e < NUM_ELVES) ->
        e_arrive ? 1;
        e++;
    :: (e == NUM_ELVES) ->
        /* Only consult if reindeer are NOT ready - this is priority */
        consulting = true;
        
        assert !(consulting && delivering);
        // We release elves here
        consulting = false;
        e = 0;
    od 

}
active proctype SantaToyDelivery()
{
    byte i = 0;
    byte j=0;
    end:
    do
    :: (i < NUM_REINDEER) ->
        r_arrive ? 1;
        i++;
        
    :: (i == NUM_REINDEER) ->
        
        delivering = true;
        // We release the reindeer here
        delivering = false;
        
        i = 0;
        
    
    od
}
