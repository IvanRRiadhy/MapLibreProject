import mkcert from 'vite-plugin-mkcert';
export default {
  server: { 
    https: true, 
    host: true,
    watch: {
      ignored: ['**/geojson/**']
    }
  },
  plugins: [mkcert()],
};
