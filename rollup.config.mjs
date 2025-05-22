import resolve from '@rollup/plugin-node-resolve';
import typescript from '@rollup/plugin-typescript';
import commonjs from '@rollup/plugin-commonjs';
import dts from 'rollup-plugin-dts';
import postcss from 'rollup-plugin-postcss';
import replace from '@rollup/plugin-replace';

export default [
  {
    input: 'src/index.ts',
    output: {
      dir: 'dist', // Use dir for output directory
      format: 'esm', // Use esm format
      sourcemap: true,
      chunkFileNames: 'chunks/chunk.[hash].js', // Naming pattern for dynamic chunks
    },
    plugins: [
      resolve({
        extensions: ['.js', '.jsx', '.ts', '.tsx'],
        skip: ['react', 'react-dom'],
      }),
      commonjs(),
      typescript({
        tsconfig: './tsconfig.json',
        exclude: ['**/*.test.tsx', '**/*.test.ts', '**/*.stories.ts'],
      }),
      replace({
        preventAssignment: true,
        'process.env.REACT_APP_ASSET_BASE_URL': JSON.stringify(
          process.env.REACT_APP_ASSET_BASE_URL,
        ),
      }),
      postcss({
        config: {
          path: './postcss.config.js',
        },
        extensions: ['.css'],
        minimize: true,
        inject: {
          insertAt: 'top',
        },
      }),
    ],
    external: ['react', 'react-dom', 'react/jsx-runtime'],
  },
  {
    input: 'dist/types/index.d.ts',
    output: [{ file: 'dist/index.d.ts', format: 'esm' }],
    plugins: [dts()],
    external: [/\.css$/],
  },
];
