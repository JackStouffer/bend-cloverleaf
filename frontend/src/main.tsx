import { render } from "preact";
import { useEffect, useState } from "preact/hooks";

type Health = "checking" | "ok" | "unavailable";

async function fetchHealth(): Promise<Health> {
  try {
    const response = await fetch("/api/health");
    return response.ok ? "ok" : "unavailable";
  } catch {
    return "unavailable";
  }
}

function App() {
  const [health, setHealth] = useState<Health>("checking");

  useEffect(() => {
    void fetchHealth().then(setHealth);
  }, []);

  return (
    <main>
      <h1>Cloverleaf</h1>
      <p>Backend: {health}</p>
    </main>
  );
}

const root = document.getElementById("app");
if (root === null) {
  throw new Error("Missing #app element");
}
render(<App />, root);
