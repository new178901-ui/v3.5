# curl_compat.py - Compatibility wrapper for curl_cffi

import httpx
import asyncio
from typing import Optional, Dict, Any

# User agent constant
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"


class ChromeSession:
    """Wrapper for httpx to work with Stripe3DSBypasser"""
    
    def __init__(self, impersonate: str = "chrome131", proxies: Optional[Dict] = None, timeout: int = 12):
        self.impersonate = impersonate
        self.proxies = proxies
        self.timeout = timeout
        self.client = None
        
    async def __aenter__(self):
        client_kwargs = {
            'timeout': httpx.Timeout(self.timeout, connect=10.0, read=20.0),
            'verify': False,
            'follow_redirects': True,
        }
        
        if self.proxies:
            proxy_url = self.proxies.get('http')
            if proxy_url:
                client_kwargs['proxy'] = proxy_url
        
        self.client = httpx.AsyncClient(**client_kwargs)
        return self
    
    async def __aexit__(self, exc_type, exc_val, exc_tb):
        if self.client:
            await self.client.aclose()
            self.client = None
    
    async def get(self, url: str, headers: Optional[Dict] = None, timeout: Optional[int] = None, 
                  allow_redirects: bool = True, **kwargs) -> Any:
        if headers is None:
            headers = {}
        headers['User-Agent'] = headers.get('User-Agent', UA)
        
        response = await self.client.get(
            url, 
            headers=headers, 
            timeout=timeout or self.timeout, 
            follow_redirects=allow_redirects
        )
        
        return self._wrap_response(response)
    
    async def post(self, url: str, data: Optional[Dict] = None, json: Optional[Dict] = None, 
                   headers: Optional[Dict] = None, timeout: Optional[int] = None, 
                   allow_redirects: bool = True, **kwargs) -> Any:
        if headers is None:
            headers = {}
        headers['User-Agent'] = headers.get('User-Agent', UA)
        
        # Convert data dict to content if provided
        content = None
        if data and isinstance(data, dict):
            from urllib.parse import urlencode
            content = urlencode(data)
        
        response = await self.client.post(
            url, 
            content=content, 
            json=json, 
            headers=headers, 
            timeout=timeout or self.timeout, 
            follow_redirects=allow_redirects
        )
        
        return self._wrap_response(response)
    
    def _wrap_response(self, response):
        """Wrap httpx response to match expected interface"""
        class ResponseWrapper:
            def __init__(self, resp):
                self.resp = resp
                self.status_code = resp.status_code
                self.url = resp.url
                self.text = resp.text
                self.content = resp.content
                self.headers = resp.headers
            
            def json(self):
                return self.resp.json()
            
            def text(self):
                return self.text
            
            def __str__(self):
                return f"<Response [{self.status_code}]>"
        
        return ResponseWrapper(response)