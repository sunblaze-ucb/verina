import { defineConfig } from 'vite'
import tailwindcss from '@tailwindcss/vite'

export default defineConfig({
  base: process.env.CF_PAGES ? '/' : '/preview/',
  plugins: [tailwindcss()],
})
