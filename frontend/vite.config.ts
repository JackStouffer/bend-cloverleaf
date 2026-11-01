import preact from "@preact/preset-vite";
import { defineConfig } from "vite";

// Development always runs behind nginx, so hot reload connects through its TLS port.
export default defineConfig({
  plugins: [preact()],
  server: {
    host: "0.0.0.0",
    port: 5173,
    strictPort: true,
    hmr: { protocol: "wss", clientPort: 8443 },
  },
});
