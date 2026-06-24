Error when talking to Gemini API Full report available at: /var/folders/tv/mjd7bwd918b7745mldgg045w0000gn/T/gemini-client-error-Turn.run-sendMessageStream-2026-05-30T13-47-21-879Z.json TerminalQuotaError: You have exhausted your capacity on this model. Your quota will reset after 15h29m54s.
    at classifyGoogleError (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/bundle/chunk-GPVT36PL.js:304203:18)
    at retryWithBackoff (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/bundle/chunk-GPVT36PL.js:304863:31)
    at process.processTicksAndRejections (node:internal/process/task_queues:105:5)
    at async GeminiChat.makeApiCallAndProcessStream (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/bundle/chunk-GPVT36PL.js:328262:28)
    at async GeminiChat.streamWithRetries (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/bundle/chunk-GPVT36PL.js:328079:29)
    at async Turn.run (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/bundle/chunk-GPVT36PL.js:328826:24)
    at async GeminiClient.processTurn (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/bundle/chunk-GPVT36PL.js:342181:22)
    at async GeminiClient.sendMessageStream (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/bundle/chunk-GPVT36PL.js:342278:14)
    at async file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/bundle/gemini-T3PINYWC.js:10871:26
    at async main (file:///opt/anaconda3/envs/claude-code/lib/node_modules/@google/gemini-cli/bundle/gemini-T3PINYWC.js:16276:5) {
  cause: {
    code: 429,
    message: 'You have exhausted your capacity on this model. Your quota will reset after 15h29m54s.',
    details: [ [Object], [Object] ]
  },
  retryDelayMs: 55794140.646886,
  reason: 'QUOTA_EXHAUSTED'
}
An unexpected critical error occurred:[object Object]
