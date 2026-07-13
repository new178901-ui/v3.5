FROM python:3.11-slim

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    gcc \
    g++ \
    make \
    libffi-dev \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# Copy requirements and install
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy main application file (required)
COPY f13.py .

# Add this line after copying f13.py
COPY p1.jpg .

# Create all data files with default content (don't try to copy them)
RUN echo '{}' > users.json && \
    echo '{}' > keys.json && \
    echo '{"active_sessions": {}, "timestamp": 0}' > session_state.json && \
    echo '{}' > pending_batches.json && \
    echo '{"daily": {}, "weekly": {}, "monthly": {}, "alltime": {}, "last_reset": {"daily": 0, "weekly": 0, "monthly": 0}}' > leaderboard.json && \
    echo '{}' > proxy_stats.json && \
    echo '{"sites": ["bradshawblanks.com"], "stats": {}, "failures": {}}' > autosopi_sites.json && \
    echo '[]' > autosopi_pending_sites.json && \
    echo '[]' > broadcast.json && \
    touch hits.txt

# Optional: Copy p1.jpg if you want to include it (remove this line if you don't have the file)
# COPY p1.jpg . 2>/dev/null || true

# Expose port
EXPOSE 8080

# Run the bot
CMD ["python", "f13.py"]
