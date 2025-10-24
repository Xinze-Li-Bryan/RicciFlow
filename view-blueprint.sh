#!/usr/bin/env bash
# View the RicciFlow blueprint in your browser

set -e

BLUEPRINT_DIR="blueprint/web"
PORT=8000

echo "🎨 RicciFlow Blueprint Viewer"
echo "=============================="
echo ""
echo "📁 Blueprint directory: $BLUEPRINT_DIR"
echo "🌐 Starting local server on port $PORT..."
echo "🔗 Open http://localhost:$PORT in your browser"
echo ""
echo "Press Ctrl+C to stop the server"
echo ""

cd "$BLUEPRINT_DIR"
python3 -m http.server $PORT
