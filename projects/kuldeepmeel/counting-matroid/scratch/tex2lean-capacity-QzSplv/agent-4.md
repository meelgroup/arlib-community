# Live Tex2Lean scheduler guidance
Epoch: 8
Mode: OPEN

This live message supersedes the capacity-at-dispatch paragraph in your brief.
Spare agent capacity is available, and the scheduler selected your proof as a useful place to expose real parallel work.
Only if library search and concrete tactic attempts have already revealed independent, substantial child lemmas: make the parent use them, put them in separately owned files, ensure every statement elaborates, try at least one proof route for each, and prove any child that closes readily. Then return a precise parallel-ready handoff so the scheduler can admit those files.
When child files are ready, do not wait until your final answer. Write the live handoff request now:
  scratch/tex2lean-capacity-QzSplv/agent-4.child-ready.json
Use exactly this JSON shape (replace the example child data):
  {"schema":"tex2lean.child-ready/2","token":"fcc083be-4035-4291-a526-c07188e14bf5","requestId":"unique-id-for-this-wave","parent":"CountingMatroid/Analysis/RestartDrawProbeCoverage.lean","children":[{"file":"Analysis/Child.lean","declarations":["Namespace.childLemma"]}],"reason":"why the child is ready"}
Choose a fresh requestId for each wave. Set REQUEST_ID to that ID, write the request, then wait for a response with that exact requestId. Keep the old response file.
List every new or changed support file you own outside the parent in children, including files whose lemmas are already proved. Name their declarations. The scheduler certifies these files together and dispatches only remaining open work; omitting a support file can reject the wave.
python3 -c 'import json, sys, time
response, request_id = sys.argv[1:]
while True:
    try:
        with open(response, encoding='\''utf8'\'') as f: ack = json.load(f)
        if isinstance(ack, dict) and ack.get('\''requestId'\'') == request_id:
            print(json.dumps(ack)); break
    except (OSError, ValueError): pass
    time.sleep(1)' 'scratch/tex2lean-capacity-QzSplv/agent-4.child-ready-result.json' "${REQUEST_ID:?set REQUEST_ID to the current requestId}"
If kind is deferred, retain ownership and preserve the decomposition. Continue useful proof work; the ticket is rechecked after writers settle. Use a fresh requestId and pause edits for any new capture. If accepted, never write released files, even if their workers are queued.
Do not manufacture lemmas, target a lemma count, or split routine tactic subgoals. If no genuine boundary has emerged, ignore the spare capacity and continue proving vertically.
