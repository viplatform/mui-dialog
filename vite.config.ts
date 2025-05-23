import peerDepsExternal from "rollup-plugin-peer-deps-external";
import dts from "vite-plugin-dts";
import { defineConfig } from "vitest/config";
import react from "@vitejs/plugin-react";

// eslint-disable-next-line @typescript-eslint/no-require-imports
const path = require("node:path");

// https://vitejs.dev/config/
export default defineConfig({
  test: {
    environment: "jsdom",
    globals: true,
  },
  resolve: {
    alias: {
      "@assets": path.resolve(__dirname, "./src/assets"),
      "@shared": path.resolve(__dirname, "./src/shared"),
      "@components": path.resolve(__dirname, "./src/components"),
    },
  },
  build: {
    target: "esnext",
    minify: true,
    lib: {
      formats: ["es"],
      entry: path.resolve(__dirname, "src/index.ts"),
      name: "fe-vi-dialog",
      fileName: (format) => {
        return `fe-vi-dialog.${format}.js`;
      },
    },
    rollupOptions: {
      output: {
        sourcemapExcludeSources: true,
        globals: {
          react: "React",
          "react/jsx-runtime": "jsxRuntime",
        },
      },
    },
  },
  plugins: [
    peerDepsExternal(),
    react(),
    dts({
      rollupTypes: true,
      exclude: ["/**/*.stories.tsx", "/**/*.test.tsx"],
    }),
  ],
});
