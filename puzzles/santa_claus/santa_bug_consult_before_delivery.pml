/*
 * santa_bug_consult_before_delivery.pml
 *
 * Buggy Santa Claus model: consulting before reindeer delivery
 * ------------------------------------------------------------
 *
 * This model intentionally violates the precedence constraint of the
 * Santa Claus concurrency puzzle: if a full group of nine reindeer is
 * waiting, Santa must serve the reindeer before consulting with elves.
 *
 *
 * An explanation of this model and how it exhibits the bug is part of
 * the blog post:
 * http://wyounas.github.io/puzzles/concurrency/2025/12/23/how-to-help-santa-claus-concurrently/
 *
 * How to run this model and see the failure:
 *
 *   1) Generate the verifier:
 *        spin -a santa_bug_consult_before_delivery.pml
 *
 *   2) Compile the verifier:
 *        gcc -O2 -o pan pan.c
 *
 *   3) Check the precedence property (with fairness enabled):
 *        ./pan -N reindeer_precedence_U -f
 *
 *      SPIN will report a violation of the LTL property.
 *
 *   4) Replay the counterexample trace:
 *        spin -t santa_bug_consult_before_delivery.pml
 *
 *      In the trace, you can see SantaConsulting enter the consulting
 *      section even though r_count == NUM_REINDEER and delivery has not
 *      yet begun, demonstrating the precedence violation.
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

active [NUM_REINDEER] proctype Reindeer()
{
    do
    :: r_arrive ! 1
    od
}

active [NUM_ELVES] proctype Elf()
{
    do
    :: e_arrive ! 1
    od
}

active proctype SantaConsulting()
{
    do
    :: (e_count < NUM_ELVES) ->
        e_arrive ? 1;
        e_count++

    :: (e_count == NUM_ELVES) ->
        consulting = true;
        consulting = false;
        e_count = 0
    od
}

active proctype SantaToyDelivery()
{
    do
    :: (r_count < NUM_REINDEER) ->
        r_arrive ? 1;
        r_count++

    :: (r_count == NUM_REINDEER) ->
        delivering = true;
        delivering = false;
        r_count = 0
    od
}


// ./pan -N reindeer_precedence_U -f

ltl reindeer_precedence_U {
    [] ( (r_count == NUM_REINDEER) -> ( (!consulting) U delivering ) )
}
