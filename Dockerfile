FROM python:3.11-slim

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    gcc \
    g++ \
    python3-dev \
    libssl-dev \
    libffi-dev \
    wget \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Install Python dependencies
COPY requirements.txt .
RUN pip install --no-cache-dir --upgrade pip
RUN pip install --no-cache-dir -r requirements.txt

# ============ INSTALL JOSERFC ============
RUN pip install joserfc

# Install playwright and browsers
RUN pip install playwright
RUN playwright install chromium
RUN playwright install-deps

# Set environment variable for playwright browsers path
ENV PLAYWRIGHT_BROWSERS_PATH=/app/.cache/ms-playwright

# Copy application
COPY . .

# Run the bot
CMD ["python", "f13.py"]
