/*
Room-based Santa Claus (Go)
==========================

This mirrors the room-based Promela/SPIN solution:

  - Reindeer and Elf goroutines try to enter their respective room by sending on an
    unbuffered channel. If the room is "closed" (not receiving), arrivals block.

  - Each room marshals a fixed-size group (9 reindeer or 3 elves). When a full group
    forms, the room sends a request to Santa and then waits for Santa's "done" signal.

  - Santa never counts arrivals. He only reacts to room requests. If both rooms have
    requests pending, reindeer have strict priority.

All channels are unbuffered, so send/receive synchronize (rendezvous), which makes the
protocol easy to reason about.

*/

package main

import (
	"context"
	"fmt"
	"sync"
	"time"
)

const (
	NumReindeer  = 9
	NumElves     = 10
	ElfGroupSize = 3
)

func Reindeer(ctx context.Context, _ int, arrive chan<- struct{}, release <-chan struct{}) {
	for {
		// Try to enter the room (blocks if the room is not receiving).
		select {
		case <-ctx.Done():
			return
		case arrive <- struct{}{}:
		}

		// Wait to be released as part of a full group.
		select {
		case <-ctx.Done():
			return
		case <-release:
		}

		// Small delay keeps the demo output readable and avoids a tight busy loop.
		time.Sleep(10 * time.Millisecond)
	}
}

func Elf(ctx context.Context, _ int, arrive chan<- struct{}, release <-chan struct{}) {
	for {
		select {
		case <-ctx.Done():
			return
		case arrive <- struct{}{}:
		}

		select {
		case <-ctx.Done():
			return
		case <-release:
		}

		time.Sleep(10 * time.Millisecond)
	}
}

// RoomReindeer collects exactly 9 arrivals, sends one request to Santa,
// waits for Santa's done signal, then releases exactly 9 reindeer.
func RoomReindeer(
	ctx context.Context,
	arrive <-chan struct{},
	release chan<- struct{},
	request chan<- struct{},
	done <-chan struct{},
) {
	round := 0
	for {
		round++

		// Collect a full team of 9.
		for i := 0; i < NumReindeer; i++ {
			select {
			case <-ctx.Done():
				return
			case <-arrive:
			}
		}

		fmt.Printf("ReindeerRoom: team #%d ready (9 reindeer)\n", round)

		// Notify Santa that a full reindeer group is ready.
		select {
		case <-ctx.Done():
			return
		case request <- struct{}{}:
		}

		// Wait until Santa finishes delivery.
		select {
		case <-ctx.Done():
			return
		case <-done:
		}

		fmt.Printf("ReindeerRoom: Santa done; releasing team #%d\n", round)

		// Release exactly this group (rendezvous: cannot race ahead).
		for i := 0; i < NumReindeer; i++ {
			select {
			case <-ctx.Done():
				return
			case release <- struct{}{}:
			}
		}
	}
}

// RoomElf collects exactly 3 arrivals, sends one request to Santa,
// waits for Santa's done signal, then releases exactly 3 elves.
func RoomElf(
	ctx context.Context,
	arrive <-chan struct{},
	release chan<- struct{},
	request chan<- struct{},
	done <-chan struct{},
) {
	round := 0
	for {
		round++

		for i := 0; i < ElfGroupSize; i++ {
			select {
			case <-ctx.Done():
				return
			case <-arrive:
			}
		}

		fmt.Printf("ElfRoom: group #%d ready (3 elves)\n", round)

		select {
		case <-ctx.Done():
			return
		case request <- struct{}{}:
		}

		select {
		case <-ctx.Done():
			return
		case <-done:
		}

		fmt.Printf("ElfRoom: Santa done; releasing group #%d\n", round)

		for i := 0; i < ElfGroupSize; i++ {
			select {
			case <-ctx.Done():
				return
			case release <- struct{}{}:
			}
		}
	}
}

// Santa responds to requests. Reindeer requests have strict priority.
// Santa does NOT marshal arrivals; he only reacts to requests.
func Santa(
	ctx context.Context,
	rRequest <-chan struct{},
	eRequest <-chan struct{},
	rDone chan<- struct{},
	eDone chan<- struct{},
) {
	rPending := false
	ePending := false

	for {
		// If nothing is pending, block until we get at least one request.
		if !rPending && !ePending {
			select {
			case <-ctx.Done():
				return
			case <-rRequest:
				rPending = true
			case <-eRequest:
				ePending = true
			}
		}

		// Drain any additional request that is already waiting right now.
		// (Both rooms can be blocked trying to send requests.)
	Drain:
		for {
			select {
			case <-rRequest:
				rPending = true
			case <-eRequest:
				ePending = true
			default:
				break Drain
			}
		}

		// Strict priority: if a reindeer group is pending, serve it first.
		if rPending {
			rPending = false
			fmt.Println("Santa: delivering toys")

			select {
			case <-ctx.Done():
				return
			case rDone <- struct{}{}:
			}
			continue
		}

		if ePending {
			// Before serving elves, re-check whether a reindeer request has become pending.
			// This matches the Promela guard: serve elves only when no reindeer request is pending.
			select {
			case <-rRequest:
				rPending = true
				continue
			default:
			}

			ePending = false
			fmt.Println("Santa: consulting with elves")

			select {
			case <-ctx.Done():
				return
			case eDone <- struct{}{}:
			}
		}
	}
}

func main() {
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()

	// Unbuffered channels = rendezvous (sender/receiver synchronize).
	rArrive := make(chan struct{})
	eArrive := make(chan struct{})
	rRelease := make(chan struct{})
	eRelease := make(chan struct{})

	rRequest := make(chan struct{})
	eRequest := make(chan struct{})

	rDone := make(chan struct{})
	eDone := make(chan struct{})

	fmt.Println("Starting Santa Claus demo...")

	var wg sync.WaitGroup

	wg.Add(1)
	go func() { defer wg.Done(); Santa(ctx, rRequest, eRequest, rDone, eDone) }()

	wg.Add(1)
	go func() { defer wg.Done(); RoomReindeer(ctx, rArrive, rRelease, rRequest, rDone) }()

	wg.Add(1)
	go func() { defer wg.Done(); RoomElf(ctx, eArrive, eRelease, eRequest, eDone) }()

	for i := 0; i < NumReindeer; i++ {
		wg.Add(1)
		go func(id int) { defer wg.Done(); Reindeer(ctx, id, rArrive, rRelease) }(i)
	}

	for i := 0; i < NumElves; i++ {
		wg.Add(1)
		go func(id int) { defer wg.Done(); Elf(ctx, id, eArrive, eRelease) }(i)
	}

	<-ctx.Done()
	fmt.Println("Stopping...")
	wg.Wait()
	fmt.Println("Done.")
}
