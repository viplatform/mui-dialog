import peerDepsExternal from "rollup-plugin-peer-deps-external";
import dts from "vite-plugin-dts";
import { defineConfig } from "vitest/config";
import react from "@vitejs/plugin-react";
import cssInjectedByJsPlugin from "vite-plugin-css-injected-by-js";

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
    minify: "terser",
    terserOptions: {
      compress: {
        drop_console: true,
        drop_debugger: true,
      },
    },
    lib: {
      formats: ["es"],
      entry: path.resolve(__dirname, "src/index.ts"),
      name: "mui-dialog",
      fileName: (format) => {
        return `mui-dialog.${format}.js`;
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
      external: [
        "react",
        "react-dom",
        "@mui/material",
        "@mui/icons-material",
        "@mui/lab",
        "@emotion/react",
        "@emotion/styled",
      ],
    },
  },
  plugins: [
    peerDepsExternal(),
    react(),
    dts({
      rollupTypes: true,
      exclude: ["/**/*.stories.tsx", "/**/*.test.tsx"],
    }),
    cssInjectedByJsPlugin(),
  ],
});
