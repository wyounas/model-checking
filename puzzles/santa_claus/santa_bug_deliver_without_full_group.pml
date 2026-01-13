/*
 * santa_bug_deliver_without_full_group.pml
 *
 * Buggy Santa Claus model: delivery without full participation
 * -------------------------------------------------------------
 *
 * This model intentionally violates one of the core constraints of the
 * Santa Claus concurrency puzzle: Santa may begin delivering toys before
 * all nine reindeer are actually harnessed.
 *
 * An explanation of this model and how it exhibits the bug is part of
 * the blog post: 
 * http://wyounas.github.io/puzzles/concurrency/2025/12/23/how-to-help-santa-claus-concurrently/
 *
 * How to run this model and see the failure:
 *
 *   1) Generate the verifier:
 *        spin -a santa_bug_deliver_without_full_group.pml
 *
 *   2) Compile the verifier:
 *        gcc -O2 -o pan pan.c
 *
 *   3) Run the verification:
 *        ./pan
 *
 *      SPIN will report a violation of the LTL property.
 *
 *   4) Replay the counterexample trace:
 *        spin -t santa_bug_deliver_without_full_group.pml
 *
 *      In the trace, you can see Santa reach `delivering = true`
 *      before all reindeer have executed their `harnessed ? 1`
 *      receives—i.e., Santa "delivers" without the full group
 *      participating together.
 * 
 */


#define NUM_REINDEER 9
#define NUM_ELVES 3

chan harnessed = [NUM_REINDEER] of { bit };
chan done_consulting = [NUM_ELVES] of { bit };

chan r_arrive = [0] of { bit };
chan e_arrive = [0] of { bit };

byte r_count = 0;
byte e_count = 0;
bool delivering = false;
bool consulting = false;

byte actually_harnessed = 0;
byte back_to_work = 0;

/* Track if reindeer are waiting */
bool reindeer_ready = false;

active [NUM_REINDEER] proctype Reindeer()
{
    do
    ::
        r_arrive ! 1;
        harnessed ? 1;
        actually_harnessed++;
        actually_harnessed--;
    od
}

active [NUM_ELVES] proctype Elves()
{
    do
    ::
        e_arrive ! 1;
        done_consulting ? 1;
        back_to_work++;
        back_to_work--;
    od
}

active proctype Santa()
{
    byte i = 0;
    byte e = 0;
    byte j;
    
    do
    :: (i < NUM_REINDEER) ->
        r_arrive ? 1;
        i++;
        if
        :: (i == NUM_REINDEER) -> reindeer_ready = true
        :: else -> skip
        fi
        
    
    :: (i == NUM_REINDEER) ->
        
        for (j : 1 .. NUM_REINDEER) {
            harnessed ! 1;
        }
        
        delivering = true;
        delivering = false;
        reindeer_ready = false;
        i = 0;
    
    :: (e < NUM_ELVES) ->
        e_arrive ? 1;
        e++;
        
    :: (e == NUM_ELVES && i < NUM_REINDEER) ->
        /* Only consult if reindeer are NOT ready - this is priority */
        consulting = true;
        for (j : 1 .. NUM_ELVES) {
            done_consulting ! 1;
        }
        consulting = false;
        e = 0;
    od
}

// /* Safety: delivering implies all reindeer harnessed */
ltl safety { [] (delivering -> actually_harnessed == NUM_REINDEER) }
